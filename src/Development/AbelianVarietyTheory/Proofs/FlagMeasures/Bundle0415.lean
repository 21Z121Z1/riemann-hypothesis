import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0073
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0412
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IoEqOfGraph
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0051

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CosetConst

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth_iff' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T)
    (a : Fin (r + 1)) : frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF; rw [dif_pos hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem zt_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    (mapLF γ F).zt = γ F.zt := by
  unfold mapLF; rw [dif_pos hγ]

theorem Xflag_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF; rw [dif_pos hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem Xsp_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF; rw [dif_pos hγ]
  show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
    (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem gmap_top (γ : S.V ≃ₗ[E] S.V) : Formalism.HermitianLatticesTheory.gmap γ (⊤ : Submodule (𝓞 E) S.V) = ⊤ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨γ.symm y, by simp⟩

end Gen

section D

variable {D : D7}

theorem nlam_top_of_nrat {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) : n ∈ NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) F :=
  ⟨⟨hn.1, gmap_top n⟩, hn.2.1, hn.2.2⟩

theorem conj_nlam_top {T : D.host.E} {G : LFlag (VS D) D.R.rS T} {γ m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hm : m ∈ NRat G) :
    γ * m * γ⁻¹ ∈ NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (mapLF γ G) := by
  obtain ⟨hi, hf, hp⟩ := hm
  have happ : ∀ y, (γ * m * γ⁻¹) (γ y) = γ (m y) := fun y => by
    show γ (m (γ.symm (γ y))) = γ (m y)
    rw [γ.symm_apply_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hi) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ),
    gmap_top _⟩, ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    have e : (γ * m * γ⁻¹) ((γ : (VS D).V →ₗ[D.host.E] (VS D).V) y) - (γ : (VS D).V →ₗ[D.host.E] (VS D).V) y =
        (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (m y - y) := by
      rw [map_sub]
      exact congrArg (· - _) (happ y)
    rw [e]
    exact Submodule.mem_map_of_mem (hf j y hy)
  · intro x hx
    have hXs := Xsp_mapLF hγ G
    have hy : γ.symm x ∈ orth (VS D) (Xsp G) := by
      rw [mem_orth_iff'] at hx ⊢
      intro w hw
      have h1 := hx (γ w) (by rw [hXs]; exact Submodule.mem_map_of_mem hw)
      have h2 := hγ w (γ.symm x)
      rw [γ.apply_symm_apply] at h2
      rw [← h2]
      exact h1
    have h3 := hp _ hy
    have e : (γ * m * γ⁻¹) x - x = (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (m (γ.symm x) - γ.symm x) := by
      show γ (m (γ.symm x)) - x = γ (m (γ.symm x) - γ.symm x)
      rw [map_sub, γ.apply_symm_apply]
    rw [e, hXs]
    exact Submodule.mem_map_of_mem h3

end D

end GlobalTheory.HL.CosetConst

namespace GlobalTheory.HL.CosetConst

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem dcrel_of_coset (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Formalism.L2.SG.TermDef.DCRel (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u)) t₀.frame t.frame := by
  have h0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have h1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hn' : n⁻¹ ∈ NRat (lf D (X.Fu u)) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn
  refine ⟨n⁻¹, nlam_top_of_nrat hn', t₀.lin * m * t₀.lin⁻¹, conj_nlam_top h0 hm, fun a => ?_, ?_⟩
  · show frame (mapLF t.lin (lf D (X.Fu u'))) a =
      n⁻¹ ((t₀.lin * m * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a))
    rw [frame_mapLF h1, frame_mapLF h0, h]
    show n.symm (t₀.lin (m _)) = n.symm (t₀.lin (m (t₀.lin.symm (t₀.lin _))))
    rw [LinearEquiv.symm_apply_apply]
  · show (mapLF t.lin (lf D (X.Fu u'))).zt =
      n⁻¹ ((t₀.lin * m * t₀.lin⁻¹) (mapLF t₀.lin (lf D (X.Fu u'))).zt)
    rw [zt_mapLF h1, zt_mapLF h0, h]
    show n.symm (t₀.lin (m _)) = n.symm (t₀.lin (m (t₀.lin.symm (t₀.lin _))))
    rw [LinearEquiv.symm_apply_apply]

theorem relevant_iff (s : TauC Y u u') :
    s.relevant ↔ Relevant D.host.F (lf D (X.Fu u)).fl s.frame.fl :=
  Formalism.L2.SG.TermDef.isRel_mk D.host.F
    (PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all D.host.F s.lam (lf D (X.Fu u))
      (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')) ⟨s.frame, s.rep.2.2.2.2⟩

theorem atPt_iff (s : TauC Y u u') (w : Point D.host.E (D.R.rS + 1)) :
    s.toTerm.atPt w ↔ Gval (lf D (X.Fu u)) s.frame ≠ 0 ∧
      IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)) w :=
  Formalism.L2.SG.TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _)
    ⟨s.frame, s.rep.2.2.2.2⟩ w

end Terms

end GlobalTheory.HL.CosetConst

namespace GlobalTheory.HL.CosetConst

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nml_eq (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    nmlOf Y u u' t = nmlOf Y u u' t₀ := by
  have hni : n⁻¹ ∈ NRat (lf D (X.Fu u)) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn
  have hmi : m⁻¹ ∈ NRat (lf D (X.Fu u')) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hm
  ext δ
  simp only [nmlOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ ha hni, m * b,
      Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hm hb, ?_⟩
    rw [h]; simp only [mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ ha hn, m⁻¹ * b,
      Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hmi hb, ?_⟩
    rw [h]; simp only [mul_assoc, mul_inv_cancel_left]

theorem G_eq_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Gval (lf D (X.Fu u)) t₀.frame = Gval (lf D (X.Fu u)) t.frame :=
  PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h)

theorem cell_iff_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m)
    (w : Point D.host.E (D.R.rS + 1)) :
    IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t₀.frame)) w ↔ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
  PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h) w

theorem rel_iff_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Relevant D.host.F (lf D (X.Fu u)).fl t₀.frame.fl ↔ Relevant D.host.F (lf D (X.Fu u)).fl t.frame.fl :=
  PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all D.host.F (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h)

theorem pt_eq (t₀ t : TauC Y u u') (hrl : t.relevant ↔ t₀.relevant) (hat : ∀ w, t.toTerm.atPt w ↔ t₀.toTerm.atPt w) :
    Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm := by
  have hCP := Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  by_cases hx : ∃ w, t₀.toTerm.atPt w ∧ t₀.toTerm.relevant
  · have hx' : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
      obtain ⟨w, hw, hr⟩ := hx
      exact ⟨w, (hat w).2 hw, hrl.2 hr⟩
    exact hCP t₀.toTerm _ _ ((hat _).1 (Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hx'))
      (Formalism.L2.SG.PairVal.ptOf_spec t₀.toTerm hx)
  · have hx' : ¬ ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
      rintro ⟨w, hw, hr⟩
      exact hx ⟨w, (hat w).1 hw, hrl.1 hr⟩
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dif_neg hx, dif_neg hx']

end GlobalTheory.HL.CosetConst

theorem GlobalTheory.HL.CosetConst.coset_const : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.MainNotions.S.Cnt.Stand D u u' →
    ∀ (t₀ t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), t₀.relevant → t₀.G ≠ 0 →
      n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m →
      t.relevant ∧ t.G = t₀.G ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm ∧
        nmlOf Y u u' t = nmlOf Y u u' t₀ ∧
        ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → (Y.tO u u').s0 t₀ t = 1 ∧ (Y.tO u u').scal t₀ t) := by
  intro D X Y u u' _ t₀ t n m hrel hG hnm
  obtain ⟨hn, hm, h⟩ := hnm
  have eG := GlobalTheory.HL.CosetConst.G_eq_frames t₀ t hn hm h
  have hrl : t.relevant ↔ t₀.relevant := by
    rw [GlobalTheory.HL.CosetConst.relevant_iff, GlobalTheory.HL.CosetConst.relevant_iff]
    exact (GlobalTheory.HL.CosetConst.rel_iff_frames t₀ t hn hm h).symm
  have hat : ∀ w, t.toTerm.atPt w ↔ t₀.toTerm.atPt w := fun w => by
    rw [GlobalTheory.HL.CosetConst.atPt_iff, GlobalTheory.HL.CosetConst.atPt_iff, eG,
      GlobalTheory.HL.CosetConst.cell_iff_frames t₀ t hn hm h w]
  have hnml := GlobalTheory.HL.CosetConst.nml_eq t₀ t hn hm h
  refine ⟨hrl.2 hrel, ?_, GlobalTheory.HL.CosetConst.pt_eq t₀ t hrl hat, hnml,
    fun hr => GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t₀ t hG hr.symm hnml.symm⟩
  rw [Formalism.L2.SG.Pf.SatGram.gterm_G (X := X) (Y := Y) (t := t),
    Formalism.L2.SG.Pf.SatGram.gterm_G (X := X) (Y := Y) (t := t₀), eG]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryFixingSpanPreservesGluedLatticesStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometryFixingSpan_preserves_gluedLattices : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  first | exact @GlobalTheory.GlueStable.glueSet_gmap_mem | exact GlobalTheory.GlueStable.glueSet_gmap_mem | (intros; apply GlobalTheory.GlueStable.glueSet_gmap_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrianStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_changedRationalFrames_of_unitriangular : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  first | exact @GlobalTheory.GenMass.changed_frames_linInd | exact GlobalTheory.GenMass.changed_frames_linInd | (intros; apply GlobalTheory.GenMass.changed_frames_linInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIdentificationEqOfGlobalLatticesEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.IotaLocal

theorem iotaGraph_eq_of_gdat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ :=
  GlobalTheory.IotaLocA.io_eq_of_graph

end GlobalTheory.Unfold.IotaLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChangeStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPairingClass_stable_unitriangularChange : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  first | exact @GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg | exact GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg | (intros; apply GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometries
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.KeyIff

variable {D : D7}

theorem one_mem {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : GV D) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

theorem dcoset_eq_iff {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (γ₁ γ₂ : GV D) :
    ({δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₁ * n'} : Set (GV D)) =
        {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} ↔
      ∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n' := by
  constructor
  · intro h
    have hm : γ₂ ∈ {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} :=
      ⟨1, one_mem F, 1, one_mem F', by simp⟩
    rw [← h] at hm
    exact hm
  · rintro ⟨n, hn, n', hn', rfl⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F hn),
        n'⁻¹ * b, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F' hn') hb, ?_⟩
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha hn, n' * b,
        Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' hn' hb, by group⟩

theorem key_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  intro D X Y u u' t t'
  have hkey : key t = key t' ↔
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ nmlOf Y u u' t = nmlOf Y u u' t' := Prod.ext_iff
  have hrow : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := by
    show rowOf Y.TR (Y.cs u) (Y.cs u') t = rowOf Y.TR (Y.cs u) (Y.cs u') t' ↔ _
    simp only [rowOf, Prod.mk.injEq, Subtype.mk.injEq]
  have hnml : nmlOf Y u u' t = nmlOf Y u u' t' ↔
      ∃ n ∈ NRat (lf D (X.Fu u)), ∃ n' ∈ NRat (lf D (X.Fu u')), t'.lin = n * t.lin * n' :=
    dcoset_eq_iff _ _ _ _
  rw [hkey, hrow, hnml]
  unfold KeyEq
  constructor
  · rintro ⟨⟨hl, hl', hi⟩, hc⟩
    exact ⟨hl, hl', hc, (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').1 hi⟩
  · rintro ⟨hl, hl', hc, hi⟩
    exact ⟨⟨hl, hl', (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').2 hi⟩, hc⟩

end GlobalTheory.Unfold.KeyIff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumRationalClassesEqProdLocalSumsStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_rationalClasses_eq_prod_localSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  first | exact @GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | exact GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | (intros; apply GlobalTheory.GenMass.tsum_classes_eq_prod_locSums <;> assumption)
end


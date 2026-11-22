import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0077
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0044
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitCons

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem haar_toReal_pos {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {U S K : Set G} (hU : IsOpen U) (hne : U.Nonempty) (h1 : U ⊆ S) (h2 : S ⊆ K)
    (hK : IsCompact K) : 0 < (μ S).toReal :=
  ENNReal.toReal_pos ((lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono h1)).ne')
    (ne_top_of_le_ne_top (hK.measure_lt_top (μ := μ)).ne (measure_mono h2))

theorem haar_toReal_pos' {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    (hμ : μ.IsHaarMeasure) {U S K : Set G} (hU : IsOpen U) (hne : U.Nonempty) (h1 : U ⊆ S) (h2 : S ⊆ K)
    (hK : IsCompact K) : 0 < (μ S).toReal := by
  haveI := hμ
  exact haar_toReal_pos μ hU hne h1 h2 hK

section Typed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X)

theorem kg_sub_kv : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KvX X p := by
  intro x hx
  simp only [MassDataIdxSteps.KgX, MassDataIdxSteps.KvX] at hx ⊢
  exact hx.1

theorem kv_facts : IsOpen (MassDataIdxSteps.KvX X p) ∧ IsCompact (MassDataIdxSteps.KvX X p) ∧
    IsOpen (MassDataIdxSteps.KgX X p) ∧ (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KgX X p := by
  obtain ⟨K, hK, ho, hc, hg⟩ := stK_holds X p
  obtain ⟨ρ, -, hρ⟩ := stRed_holds X p K hK
  refine ⟨by rw [← hK]; exact ho, by rw [← hK]; exact hc, hg, ?_⟩
  have h1 := (hρ 1).mp (map_one ρ)
  simpa using h1

theorem kg_sub_kpp : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KppX X hb p := by
  intro x hx
  obtain ⟨K, hK, -⟩ := stK_holds X p
  obtain ⟨ρ, hs, hρ⟩ := stRed_holds X p K hK
  obtain ⟨A, hA, hker, -⟩ := stImA_holds X hb p K hK ρ hs hρ
  have hxK : x ∈ (K : Set (MassDataIdxSteps.HAp X p)) := by
    rw [hK]
    exact kg_sub_kv X p hx
  rw [← hA]
  exact ⟨⟨x, hxK⟩, hker (MonoidHom.mem_ker.mpr ((hρ ⟨x, hxK⟩).mpr hx)), rfl⟩

theorem kpp_sub_kv : MassDataIdxSteps.KppX X hb p ⊆ MassDataIdxSteps.KvX X p := by
  obtain ⟨K, hK, -⟩ := stK_holds X p
  obtain ⟨ρ, hs, hρ⟩ := stRed_holds X p K hK
  obtain ⟨A, hA, -⟩ := stImA_holds X hb p K hK ρ hs hρ
  intro x hx
  rw [← hA] at hx
  obtain ⟨y, -, rfl⟩ := hx
  rw [← hK]
  exact y.2

theorem kg_sub_knat (u : D.what₂.Word) : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KnatX X u p := by
  intro y hy
  have h1 : (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KvX X p := kg_sub_kv X p (kv_facts X p).2.2.2
  exact ⟨hy.1, 1, y, (Ssub _ _ _ _).one_mem, h1, hy, (one_mul y).symm⟩

theorem knat_sub_kv (u : D.what₂.Word) : MassDataIdxSteps.KnatX X u p ⊆ MassDataIdxSteps.KvX X p := fun _ h => h.1

end Typed

section Typed2

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X)

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures in

theorem level_compression_chain (u : D.what₂.Word) :
    MassDataIdxSteps.KgX X p ⊆ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ∧
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ⊆ MassDataIdxSteps.KvX X p := by
  obtain ⟨K, hK, -, -, -⟩ := MassDataIdxSteps.stK_holds X p
  obtain ⟨ρ, -, hker⟩ := stRed_holds X p K hK
  have hKf := (PIW.MassDataColumns.finHA_mem_Kf_iff X hb (X.xu u)).2 (X.xu_K u)
  rw [Kf, Subgroup.mem_iInf] at hKf
  have haK : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) ∈ MassDataIdxSteps.KvX X p := hKf p.1
  have hcs : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
      (fun z => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) * z *
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)))⁻¹) ''
        MassDataIdxSteps.KppX X hb p := by
    unfold compSet K2u MassDataIdxSteps.KppX compSet
    rw [Set.image_image, Set.image_image]
    congr 1
    funext y
    rw [map_mul, map_mul, map_inv]
  rw [hcs]
  generalize haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) = a at haK ⊢
  have haK' : a ∈ (K : Set (MassDataIdxSteps.HAp X p)) := by rw [hK]; exact haK
  constructor
  · intro k hk
    have hkK : k ∈ (K : Set (MassDataIdxSteps.HAp X p)) := hK ▸ kg_sub_kv X p hk
    have h2 := (hker ((⟨a, haK'⟩ : K)⁻¹ * ⟨k, hkK⟩ * ⟨a, haK'⟩)).1
      (by rw [map_mul, map_mul, (hker ⟨k, hkK⟩).2 hk, mul_one, map_inv, inv_mul_cancel])
    have h2' : a⁻¹ * k * a ∈ MassDataIdxSteps.KgX X p := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
    refine ⟨a⁻¹ * k * a, kg_sub_kpp X hb p h2', ?_⟩
    group
  · rintro _ ⟨z, hz, rfl⟩
    have hzK : z ∈ (K : Set (MassDataIdxSteps.HAp X p)) := hK ▸ kpp_sub_kv X hb p hz
    rw [← hK]
    exact K.mul_mem (K.mul_mem haK' hzK) (K.inv_mem haK')

end Typed2

section Glob

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem conjugated_level_open_one_mem (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) : IsOpen (K2u X hb u) ∧ (1 : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u ∧
    K2u X hb u ⊆ (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := PIW.MassDataColumns.isTopGroup_HA (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.sig X.B.I.J
  set e := Formalism.L2.SG.Pf.Meas.eFin X.B.I hb
  have h1 : IsOpen (levelUnitary X hb) := by
    have hk : levelUnitary X hb = e '' X.K2 := rfl
    rw [hk]
    exact e.toHomeomorph.isOpenMap _ (Formalism.L2.SG.Pf.level_subgroup_compact_open X).1
  set a := finHA X hb (X.xu u)
  have hc : K2u X hb u = ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)) '' levelUnitary X hb := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]
    exact ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isOpenMap _ h1
  · refine ⟨finHA X hb 1, ⟨1, hK.1, rfl⟩, ?_⟩
    show a * finHA X hb 1 * a⁻¹ = 1
    rw [finHA_eq_eFin, map_one, mul_one, mul_inv_cancel]
  · rintro _ ⟨y, ⟨k, hk2, rfl⟩, rfl⟩
    have hxu : a ∈ MassDataMassesW.KX X := (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
    have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
      (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
    exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

theorem closed_SNH_X (u : D.what₂.Word) :
    IsClosed (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsClosed (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsClosed (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact PI.LevelKSplit.W.ExC.closed_SNH (MassDataVolumesW.stepHerm X) (fun x => star_star x) (frameOf X u) _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u)

end Glob

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem sv_pos (w : D.what₂.Word) (p : TypX X) {S : Set (MassDataIdxSteps.HAp X p)}
    (h1 : MassDataIdxSteps.KgX X p ⊆ S) (h2 : S ⊆ MassDataIdxSteps.KvX X p) :
    0 < ((X.measW w).μSv p.1 (Subtype.val ⁻¹' S)).toReal := by
  haveI := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  obtain ⟨-, hc, hgo, h1g⟩ := kv_facts X p
  have hcl := MassDataLevelSSteps.LatTop.isClosed_Ssub (v := p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)
  exact haar_toReal_pos _ (hgo.preimage continuous_subtype_val)
    ⟨1, show (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KgX X p from h1g⟩
    (Set.preimage_mono h1) (Set.preimage_mono h2) (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc)

theorem gv_pos (p : TypX X) {S : Set (MassDataIdxSteps.HAp X p)}
    (h1 : MassDataIdxSteps.KgX X p ⊆ S) (h2 : S ⊆ MassDataIdxSteps.KvX X p) :
    0 < (X.measG.μGv p.1 S).toReal := by
  haveI := X.measG_norm.2.2.2.1 p.1
  obtain ⟨-, hc, hgo, h1g⟩ := kv_facts X p
  exact haar_toReal_pos _ hgo ⟨1, h1g⟩ h1 h2 hc

theorem locHaarPosC_holds : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hKc := kCompactOpen_holds X
  have hKcs : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Ssub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).1.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have hKcn : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).2.1.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have hKch : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).2.2.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have h1K : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    (MassDataMassesW.KX X).one_mem
  refine ⟨fun p => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gv_pos X p (kg_sub_kv X p) subset_rfl
  · exact gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)
  · exact gv_pos X p (kg_sub_kpp X hb p) (kpp_sub_kv X hb p)
  · exact sv_pos X u p (kg_sub_kv X p) subset_rfl
  · exact sv_pos X u' p (kg_sub_kv X p) subset_rfl
  · exact sv_pos X u p (level_compression_chain X hb p u).1 (level_compression_chain X hb p u).2
  · exact sv_pos X u' p (level_compression_chain X hb p u').1 (level_compression_chain X hb p u').2
  · haveI := X.measG_norm.2.2.1
    exact haar_toReal_pos _ hKc.2 ⟨1, h1K⟩ subset_rfl subset_rfl hKc.1
  · haveI := (X.measW_norm u).2.2.2.2.2.2.1
    exact haar_toReal_pos _ (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcs u)
  · haveI := (X.measW_norm u').2.2.2.2.2.2.1
    exact haar_toReal_pos _ (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcs u')
  · exact haar_toReal_pos' _ (X.measW_norm u).2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKch u)
  · exact haar_toReal_pos' _ (X.measW_norm u').2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKch u')
  · obtain ⟨ho, h1, hs⟩ := conjugated_level_open_one_mem X hb hK u
    exact haar_toReal_pos' _ (X.measW_norm u).2.2.1 (ho.preimage continuous_subtype_val) ⟨1, h1⟩ subset_rfl (Set.preimage_mono hs) (hKch u)
  · obtain ⟨ho, h1, hs⟩ := conjugated_level_open_one_mem X hb hK u'
    exact haar_toReal_pos' _ (X.measW_norm u').2.2.1 (ho.preimage continuous_subtype_val) ⟨1, h1⟩ subset_rfl (Set.preimage_mono hs) (hKch u')
  · exact haar_toReal_pos' _ (X.measW_norm u).2.2.2.2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcn u)
  · exact haar_toReal_pos' _ (X.measW_norm u').2.2.2.2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcn u')

end Main

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

def SDLocX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def UnramTypX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), TypAt X v → UnramAt (E := X.B.I.E) v

def STypIdx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X), X.MeasTie hb →
    ((X.measW u).μSv p.1).IsHaarMeasure →
    ((X.measW u).μSv p.1 (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1)).toReal =
      ((glkC D.R.k (gOf p) : ℕ) : ℝ) / ((ukC D.R.k (gOf p) : ℕ) : ℝ) *
        ((X.measW u).μSv p.1 (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1)).toReal

theorem gAt_mem {D : D7} (X : HidaSetting D) (p : TypX X) : ((gAt X p.1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  obtain ⟨p, hp⟩ := p
  have hT : IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p := by
    unfold typSet at hp
    split_ifs at hp with hfin
    · simpa using hp
    · simp at hp
  unfold gAt
  split_ifs with h0
  · exact h0
  · unfold IsTyped at hT
    exact hT.resolve_left h0

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inTypedC_loc (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) (hψ : IsCharAF X.B.I.F ψ) (hψs : IsStdChar ψ) :
    InTypedC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro hX _hP hL hL' hTF p
  have hlat : ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧
      (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩
  have hTyp : TypAt X p.1 := p.2
  refine ⟨?_, hI X hb u p hX.1 (hL p.1).2.1, hI X hb u' p hX.1 (hL' p.1).2.1⟩
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ p.1 (gAt X p.1) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hψs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (hSD X p.1) (hUn X p.1 hTyp) hlat (hTF p).1 (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL p.1).1 _ (hL p.1).2.1 (hL p.1).2.2.1 _ (hL' p.1).2.1 (hL' p.1).2.2.1 (hL p.1).2.2.2 (hL' p.1).2.2.2
  show MX X u u' ψ p.1 / localVolumeUnit X ψ p.1 = _
  unfold MX localVolumeUnit OmX
  rw [if_pos hTyp, if_pos hTyp]
  exact h

theorem typedAll_of (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  exact inTypedC_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSD hUn hI T.ψ_char T.ψ_std

theorem typedAll_of_idx (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll :=
  typedAll_of (fun X v => Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v)
    (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) hI

end Main

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgmPinvEq
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem qbar_qbar (q : FreeE w) : qbar w (qbar w q) = q := by
  apply Subtype.ext
  simp only [qbar, pinv_pinv]

theorem hgt_qbar (q : FreeE w) : hgt w (qbar w q) = hgt w q := by
  unfold hgt qbar
  have h1 := pinv_add w q.1.1 q.1.2 q.2.2
  have h2 : q.1.1.val < q.1.2.val := q.2.1
  simp only
  omega

theorem sgm_pinv_eq (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm (pinv w c) (pinv w a) = (sgm a c : D.host.E) := by
  have h := sgm_pinv w a c hs
  rcases sgm_cases a c with e | e
  · rw [e, one_mul] at h; rw [h, e]
  · rw [e] at h ⊢; linear_combination -h

theorem sgq_qbar (q : FreeE w) : sgq w (qbar w q) = sgq w q :=
  sgm_pinv_eq w q.1.1 q.1.2 q.2.2

theorem Xinv_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y)⁻¹ q.1.1 q.1.2 = cf w y q - y q := by
  have h := inv_diff (Xmat_upU w y) (Xmat_upU w (trunc w y (hgt w q))) q.2.1 (fun i j hij hh => by
    by_cases hb : i < j ∧ blkOf w.1 i.val = blkOf w.1 j.val
    · simp only [Xmat, ne_of_lt hij, if_false, dif_pos hb, trunc]
      rw [if_pos (show hgt w ⟨(i, j), hb⟩ < hgt w q from hh)]
    · simp only [Xmat, ne_of_lt hij, if_false, dif_neg hb])
  rw [Xmat_q, Xmat_q] at h
  have h0 : trunc w y (hgt w q) q = 0 := by unfold trunc; rw [if_neg (lt_irrefl _)]
  rw [h0] at h
  unfold cf
  linear_combination h

theorem cf_mem (y : FreeE w → D.host.E) (q : FreeE w)
    (hy : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p)) : cf w y q ∈ ddPow D (hgt w q) := by
  unfold cf
  refine grD_inv (Xmat_upU w _) (Xmat_grD w _ fun p => ?_) q.1.1 q.1.2 (le_of_lt q.2.1)
  unfold trunc
  split_ifs with h
  · exact hy p h
  · exact FractionalIdeal.zero_mem _

theorem E_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 =
      y q - sgq w q * D.conjF (cf w y (qbar w q) - y (qbar w q)) := by
  rw [Matrix.sub_apply, Xmat_q]
  have h := Xinv_q w y (qbar w q)
  simp only [Psi]
  rw [show (Xmat w y)⁻¹ (pinv w q.1.2) (pinv w q.1.1) = cf w y (qbar w q) - y (qbar w q) from h]
  rfl

theorem condX_third (X : MatR D) (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) = (X - Psi w X⁻¹) (pinv w c) (pinv w a) := by
  rw [Matrix.sub_apply]
  simp only [Psi, pinv_pinv]
  rw [sgm_pinv_eq w a c hs]
  simp only [bt, sgm, map_mul, map_pow, map_neg, map_one]
  ring

theorem bt_mem {X : MatR D} (hG : GrD X) (a c : Fin (D.R.rS + 1)) (hac : a < c) :
    bt D X a c ∈ ddPow D (c.val - a.val) := by
  have h := hG a c (le_of_lt hac)
  rw [show bt D X a c = sgm a c * X a c by simp only [bt, sgm]; ring]
  rcases sgm_cases a c with e | e
  · rw [e, one_mul]; exact h
  · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h

theorem condX_iff (y : FreeE w → D.host.E) :
    CondX w (Xmat w y) ↔ (∀ q, y q ∈ ddPow D (hgt w q)) ∧
      ∀ q, (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
  constructor
  · intro h
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      intro q
      obtain ⟨h1, -, -⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
      have e := hgt_qbar w q
      unfold hgt at e
      simp only [qbar, pinv_pinv] at h1 e
      rw [e, Xmat_q] at h1
      exact h1
    refine ⟨hy, fun q => ?_⟩
    obtain ⟨-, -, h3⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
    rw [condX_third w _ _ _ (qbar w q).2.2] at h3
    have e := hgt_qbar w q
    unfold hgt at e
    simp only [qbar, pinv_pinv] at h3 e
    rw [e] at h3
    exact h3
  · rintro ⟨hy, hE⟩ a c hac hs
    have hG := grD_inv (Xmat_upU w y) (Xmat_grD w y hy)
    set p : FreeE w := qbar w ⟨(a, c), hac, hs⟩ with hp
    have hpe : hgt w p = c.val - a.val := hgt_qbar w _
    have hp1 : Xmat w y (pinv w c) (pinv w a) = y p := Xmat_q w y p
    refine ⟨?_, bt_mem hG a c hac, ?_⟩
    · rw [hp1, ← hpe]; exact hy p
    · rw [condX_third w _ a c hs, ← hpe]; exact hE p

end Formalism.L2.SG.Pf.StabIntLat
end
end


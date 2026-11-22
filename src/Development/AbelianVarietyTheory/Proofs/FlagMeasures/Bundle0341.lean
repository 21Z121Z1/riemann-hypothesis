import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulMemOfOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbability
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.FibProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem spH_B (x y : S.V) : (spH S).B x y = S.hT y x := rfl

theorem frF_e (F : FlagG S r T) (hT : T ≠ 0) (a : Fin (r + 1)) : (frF F hT).e a = F.fvec a := rfl

theorem frF_Xa (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (frF F hT).Xa k = F.Xa k := by

  have h : (fun b : Fin r => (frF F hT).e b.castSucc) = F.e := by
    funext b
    simp [frF_e, FlagG.fvec]
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, h, FlagG.Xa]

theorem frF_X (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.X, frF_Xa, FlagG.Xa, FlagG.X]
  congr 1
  ext x
  simp

end Gen

section Bridge
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem isom_of_B {n : S.V ≃ₗ[E] S.V} (h : ∀ x y, (spH S).B (n x) (n y) = (spH S).B x y) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  have h1 := h y x
  rw [spH_B, spH_B] at h1
  exact h1

theorem gmap_eq_smul (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap n Λ = n • Λ := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem nlam_of_inN (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : (frF F hT).InN (n : S.V →ₗ[E] S.V)) (hΛ : n • Λ = Λ) : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T) := by
  obtain ⟨hB, -, he, hperp⟩ := h

  have hfe : ∀ b : Fin r, (frF F hT).e b.castSucc = F.e b := fun b => by
    simp [frF_e, FlagG.fvec]
  refine ⟨⟨isom_of_B hB, (gmap_eq_smul n Λ).trans hΛ⟩, ?_, ?_⟩
  ·
    intro j x hx
    have hle : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < j + 1 := hb
      have h3 := he b
      rw [hfe, frF_Xa] at h3
      have hmono : F.Xa b.val ≤ F.Xa j :=
        Submodule.span_mono (Set.image_mono fun i (hi : i.val < b.val) => show i.val < j by omega)
      exact hmono h3
    simpa using hle hx
  ·
    intro y hy
    have hy' : ∀ x ∈ F.X, S.hT x y = 0 := by
      intro x hx
      have := (Submodule.mem_iInf _).mp hy x
      simpa using (Submodule.mem_iInf _).mp this hx
    have h4 := hperp y (fun a => by
      rw [hfe]
      have h5 := (spH S).herm y (F.e a)
      rw [spH_B, hy' _ (Submodule.subset_span (Set.mem_range_self a)), star_zero] at h5
      exact h5.symm)
    rw [frF_X] at h4
    exact h4

end Bridge

def mapD {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F : Formalism.HermitianLatticeCounting.S6.FlagD H r) (φ : V ≃ₗ[K] V) (hφ : ∀ x y, H.B (φ x) (φ y) = H.B x y) : Formalism.HermitianLatticeCounting.S6.FlagD H r where
  e a := φ (F.e a)
  T := F.T
  indep := F.indep.map' (φ : V →ₗ[K] V) (LinearEquiv.ker φ)
  iso a b := by rw [hφ]; exact F.iso a b
  zperp a := by rw [hφ]; exact F.zperp a
  zz := by rw [hφ]; exact F.zz
  hT := F.hT

section Obj
variable {D : D7} {X : HidaSetting D}

theorem Ft_e {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (a : Fin (D.R.rS + 1)) :
    (Ft t).e a = t.lin ((F0 X u).e a) := by
  have h : t.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  change (frq X t.rep).fl.fvec a = t.rep.1.2 ((X.Fu u).fvec a)
  simp only [frq, mapLF, h, dite_true]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

theorem Ft_Xa {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (k : ℕ) :
    (Ft t).Xa k = ((F0 X u).Xa k).map (t.lin : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, Submodule.map_span, Set.image_image, Ft_e, LinearEquiv.coe_coe]

end Obj

theorem mem_line {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {A : Submodule (𝓞 K) K} {v : V} {t : K} (ht : t ∈ A) :
    t • v ∈ GlobalTheory.DegCnt.line A v := by
  exact Submodule.mem_map.mpr ⟨t, ht, by simp⟩

section Main
variable {D : D7} {X : HidaSetting D}

theorem line_e_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (a : Fin D.R.rS) :
    GlobalTheory.DegCnt.line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_iSup (fun b => GlobalTheory.DegCnt.line (N.aa b) (N.F.e b.castSucc)) a)))

theorem line_z_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) : GlobalTheory.DegCnt.line 1 N.F.z ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left le_sup_right

theorem stab_of_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  have he : ∀ b, a ((X.Fu u).e b) = (X.Fu u).e b := fun b => by
    have h : a ((X.Fu u).fvec b.castSucc) = (X.Fu u).fvec b.castSucc := hfix b.castSucc
    simpa [FlagG.fvec] using h
  have hz : a (X.Fu u).z = (X.Fu u).z := by
    have h : a ((X.Fu u).fvec (Fin.last _)) = (X.Fu u).fvec (Fin.last _) := hfix (Fin.last _)
    simpa [FlagG.fvec] using h
  refine ⟨hi, fun j => ?_, hz⟩
  rw [FlagG.Xa, Submodule.map_span, Set.image_image]
  simp [he]

theorem gmap_one' (L : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  rw [gmap_eq_smul, one_smul]

end Main

theorem fibC : FibC := by
  intro D large₂ X Y u hStd t₁ t₂ hlam hEq
  obtain ⟨n₀, hnN, hnΛ, hnG⟩ := hEq

  have hi₁ : t₁.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₁.rep.2.2.1
  have hi₂ : t₂.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₂.rep.2.2.1
  have hin : n₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := isom_of_B hnN.1
  have hg₁ : t₁.lin • t₁.lam' = t₂.lam := by
    rw [← gmap_eq_smul, ← hlam]
    exact t₁.rep.2.2.2.1
  have hg₂ : t₂.lin • t₂.lam' = t₂.lam := by
    rw [← gmap_eq_smul]
    exact t₂.rep.2.2.2.1
  have hnΛ' : n₀ • t₂.lam = t₂.lam := hlam ▸ hnΛ

  obtain ⟨g, hg⟩ : ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, g = t₂.lin⁻¹ * n₀ * t₁.lin := ⟨_, rfl⟩
  have hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hg ▸ mul_mem (mul_mem (inv_mem hi₂) hin) hi₁
  have hgB : ∀ x y, (HV D).B (g x) (g y) = (HV D).B x y := fun x y => by
    rw [spH_B, spH_B]
    exact hgi y x
  have hgl : g • t₁.lam' = t₂.lam' := by
    rw [hg, mul_smul, mul_smul, hg₁, hnΛ', ← hg₂, inv_smul_smul]
  have hgmem : ∀ x ∈ t₁.lam', g x ∈ t₂.lam' := fun x hx => by
    have h := Submodule.smul_mem_pointwise_smul x g t₁.lam' hx
    rw [hgl] at h
    exact h

  let G : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := mapD (F0 X u) g hgB
  have hSG : GlobalTheory.DegAsm.SameGr (F0 X u) G := by
    intro a
    have h := hnG a
    rw [Ft_e, Ft_e, Ft_Xa, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at h
    show g ((F0 X u).e a) - (F0 X u).e a ∈ (F0 X u).Xa a.val
    rw [hg]
    exact h

  obtain ⟨N₁, hF₁, -, -, -, hd₁, -, hRef₁, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₁.lam' (Or.inl t₁.mem')
  obtain ⟨N₂, hF₂, -, -, -, hd₂, hTm₂, hRef₂, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₂.lam' (Or.inl t₂.mem')
  have hP₁ : N₁.P0 ≤ t₁.lam' :=
    (show N₁.P0 ≤ N₁.Ref (GlobalTheory.HermLat.latL N₁.F N₁.F' t₁.lam') from le_sup_left).trans hRef₁.le
  have hP₂ : N₂.P0 ≤ t₂.lam' :=
    (show N₂.P0 ≤ N₂.Ref (GlobalTheory.HermLat.latL N₂.F N₂.F' t₂.lam') from le_sup_left).trans hRef₂.le
  have haa : ∀ a, N₂.aa a = N₁.aa a := fun a => by
    simp only [GlobalTheory.DegCnt.NF.aa, hd₁, hd₂]
  have he₁ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₁.lam' := by
    intro a s hs
    have h := hP₁ (line_e_le N₁ a (mem_line (v := N₁.F.e a.castSucc) ((haa a) ▸ hs)))
    rwa [hF₁] at h
  have he₂ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    have h := hP₂ (line_e_le N₂ a (mem_line (v := N₂.F.e a.castSucc) hs))
    rwa [hF₂] at h
  have hone : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hz₁ : (F0 X u).z ∈ t₁.lam' := by
    have h := hP₁ (line_z_le N₁ (mem_line (v := N₁.F.z) hone))
    rwa [one_smul, hF₁] at h
  have hz₂ : (F0 X u).z ∈ t₂.lam' := by
    have h := hP₂ (line_z_le N₂ (mem_line (v := N₂.F.z) hone))
    rwa [one_smul, hF₂] at h
  have hU₂ : GlobalTheory.HermLat.IsUnimod (HV D) t₂.lam' := hTm₂.1.1
  have hFr₂ : GlobalTheory.HermLat.IsFrame (F0 X u) t₂.lam' N₂.aa := hF₂ ▸ hTm₂.1.2.1
  have hint : ∀ a, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' ∧ s • G.e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    refine ⟨he₂ a s hs, ?_⟩
    have h := hgmem _ (he₁ a s hs)
    rw [map_smul] at h
    exact h
  have hGz : G.z ∈ t₂.lam' := hgmem _ hz₁

  have hK := (GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd).1
  obtain ⟨m, hmN, hmΛ, hmE⟩ := GlobalTheory.DegAsm.FrameMove.main D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) G N₂.aa
    t₂.lam' hU₂ hFr₂ hSG rfl hint hz₂ hGz

  have hai : g⁻¹ * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hgi) (isom_of_B hmN.1)
  have hafix : ∀ b, (g⁻¹ * m) ((F0 X u).e b) = (F0 X u).e b := fun b => by
    show g.symm (m ((F0 X u).e b)) = (F0 X u).e b
    rw [hmE b]
    exact g.symm_apply_apply _
  have hamap : (g⁻¹ * m) • t₂.lam' = t₁.lam' := by
    rw [mul_smul, hmΛ, ← hgl, inv_smul_smul]

  have hrow := (Y.rowsOK u).2 t₁.lam' ((Y.rowsOK u).1 _ t₁.mem')
  have hl : t₂.lam' = t₁.lam' :=
    hrow.unique ⟨t₂.mem', g⁻¹ * m, stab_of_fix u hai hafix, (gmap_eq_smul _ _).trans hamap⟩
      ⟨t₁.mem', 1, stab_of_fix u (one_mem _) (fun _ => rfl), gmap_one' _⟩
  refine ⟨hl.symm, n₀, g⁻¹ * m, nlam_of_inN (X.Fu u) (tu_ne D u) hnN hnΛ, hai, ?_, hafix, m⁻¹, ?_, ?_⟩
  · rw [gmap_eq_smul]
    rw [hl] at hamap
    exact hamap
  · have hmΛ' : m • t₁.lam' = t₁.lam' := by
      rw [← hl]
      exact hmΛ
    exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam (nlam_of_inN (X.Fu u) (tu_ne D u) hmN hmΛ')
  · rw [hg]
    group

end GlobalTheory.TypeAsm.FibProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFinsetOfMemNhds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open Filter Topology
open scoped TensorProduct

namespace GlobalTheory.ThetaVacuumAE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finset_of_mem_nhds {F : Type} [Field F] [NumberField F] {N : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)} (hN : N ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ α ∈ intAf F, (∀ v ∈ S, evalV F v α = 0) → α ∈ N := by
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have h := hc.tendsto (fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) hN
  have h' := mem_map.1 h
  rw [nhds_pi, mem_pi'] at h'
  obtain ⟨I, t, ht, hI⟩ := h'
  refine ⟨I, fun α hα h0 => ?_⟩
  have hm : (fun w => (⟨evalV F w α, hα w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈
      Set.pi (I : Set (HeightOneSpectrum (𝓞 F))) t := by
    intro w hw
    have := mem_of_mem_nhds (ht w)
    convert this using 2
    exact h0 w hw
  exact hI hm

theorem fg_int {E : Type} [Field E] [NumberField E] {M : Submodule (𝓞 E) E} (h : M.FG) : (M.restrictScalars ℤ).FG :=
  Submodule.FG.restrictScalars h

theorem exists_fg_coord {D : D7} (V : HSp D) :
    ∃ M : Submodule ℤ D.host.E, M.FG ∧ ∀ x ∈ L0c D V, ∀ i, x i ∈ M ∧ star (x i) ∈ M := by
  let P : Submodule (𝓞 D.host.E) D.host.E := ⨆ i, V.L0.map ((V.frame.coord i).restrictScalars (𝓞 D.host.E))
  have hP : P.FG := Submodule.fg_iSup _ fun i => V.standardTuple_isLattice.fg.map _
  have hx : ∀ x ∈ L0c D V, ∀ i, x i ∈ P := fun x hx i =>
    Submodule.mem_iSup_of_mem i ⟨_, hx, by simp [Finsupp.single_apply]⟩
  let c : D.host.E →ₗ[ℤ] D.host.E := (starRingEnd D.host.E).toAddMonoidHom.toIntLinearMap
  refine ⟨P.restrictScalars ℤ ⊔ (P.restrictScalars ℤ).map c, (fg_int hP).sup ((fg_int hP).map c), fun x h i =>
    ⟨Submodule.mem_sup_left (hx x h i), Submodule.mem_sup_right ⟨x i, hx x h i, rfl⟩⟩⟩

theorem continuous_tmul (D : D7) (e : D.host.E) :
    Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) := by
  have hp : Continuous fun β : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 β := continuous_const.prodMk continuous_id
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h := hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D)))
  refine h.congr fun α => ?_
  simp only [Pi.smul_apply', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.ThetaVacuumAE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

theorem exists_orthonormal_frame_of_le : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ S : Submodule ℂ (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), S ≤ B.I.HomS B.σs B.μf B.fund B.R → FiniteDimensional ℂ S → ∃ T : Fin (Module.finrank ℂ S) → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ S) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ ∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0 := by
  intro B d hd S hle hfin
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  obtain ⟨-, -, hR, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs
      map_one' := hU.1
      map_mul' := hU.2.1 }
  obtain ⟨T, h1, h2, h3, -⟩ := exists_frame S (B.tens B.w) fun T hT T' hT' u u' =>
    inner_intertwiners σ hU.2.2.1 hirr (fun g => B.R (g, 1)) (fun g => hR _) _ hw T T' (hle hT) (hle hT') u u'
  exact ⟨T, h1, h2, h3⟩

end GlobalTheory.IntertwinerFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfSteps
section
noncomputable section

open scoped Classical
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

theorem exists_row_level_analytic (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticP) : StepAnalyticConstantsP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀),
    fun C' Cl e1 e2 D large₂ X Y u u' hTies hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, hBk',
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hTies hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'⟩

end GlobalTheory.NGRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbabilityStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability : ∀ (j : ℕ) (μ : Measure (PI.MtM j)), PI.IsHaarOnM (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ → μ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ (ENNReal.ofReal (volUn j)⁻¹) := by
  first | exact @GlobalTheory.UnitaryVolume.hasDens_unitary | exact GlobalTheory.UnitaryVolume.hasDens_unitary | (intros; apply GlobalTheory.UnitaryVolume.hasDens_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcExistsAll
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem hcExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), HcExists D F := by
  intro D F X u wt ιA h0 hW hA c
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u wt ιA hW hA (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA)
  exact ⟨Φ.symm ((F u).cls0.y c * h0⁻¹), (hΦ _ _).2 (Φ.apply_symm_apply _)⟩

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocalStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_completedLattice_eq_finprod_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E, {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X = ∏ᶠ v : HeightOneSpectrum (𝓞 F), {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  first | exact @GlobalTheory.AdelicU.indicator_latHat_eq_finprod | exact GlobalTheory.AdelicU.indicator_latHat_eq_finprod | (intros; apply GlobalTheory.AdelicU.indicator_latHat_eq_finprod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugationStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdeleIso_commutes_with_conjugation : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  first | exact @GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | exact GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | (intros; apply GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateOfSets
section
open MeasureTheory NumberField Matrix
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms

noncomputable section

namespace GlobalTheory.GlobalProjectorCompare

section Test

variable (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
  [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)

end Test

def AutomorphicCountingData (n₀ : ℕ) (A : ℝ) (I : AutInst) (lam : InfinitePlace I.F → Fin I.n → ℝ) (μf : Measure I.Gf)
    (e : I.Gf → ℂ) : Prop :=
  ∃ (b : ℝ) (g g₀ : ℕ), HidaSetting I n₀ A b lam μf g g₀ e

def LowGapIntegrable (n₀ : ℕ) (A : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) →
    Integrable (phOf I σ w) (Measure.pi fun v => Formalism.REAL.muG (I.ε v))

def FiniteHom (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) →
    (∀ v, C * (I.n : ℝ) ^ 2 * Real.sqrt (q0At I v : ℝ) ≤ h) →
    FiniteDimensional ℂ (I.eHom σs μf fund R Re)

def PointwiseCusp (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) →
    (∀ v, C * (I.n : ℝ) ^ 2 * Real.sqrt (q0At I v : ℝ) ≤ h) →
    ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConv μf fund R (phe I (phOf I σ w) e) T →
      ∀ Fv ∈ LinearMap.range (T : I.L2 μf fund →ₗ[ℂ] I.L2 μf fund), IsCuspClass I μf fund Fv

variable (I : AutInst)

def oneStep (W : Submodule I.E (Fin I.n → I.E)) : ℕ → Submodule I.E (Fin I.n → I.E) :=
  fun i => if i = 0 then ⊥ else W

end GlobalTheory.GlobalProjectorCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalL2BoundHeightStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_L2_bound_height : ∀ (B : RowsAut) (U : Set B.I.GA), 1 ≤ B.I.n → IsCompact U → (∀ u ∈ U, u.2 ∈ B.I.Kset) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA), ∫⁻ g in U, (‖B.I.ext y (x * g)‖₊ : ENNReal) ^ 2 ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2) := by
  first | exact @GlobalTheory.LocMass.local_mass_le | exact GlobalTheory.LocMass.local_mass_le | (intros; apply GlobalTheory.LocMass.local_mass_le <;> assumption)
end


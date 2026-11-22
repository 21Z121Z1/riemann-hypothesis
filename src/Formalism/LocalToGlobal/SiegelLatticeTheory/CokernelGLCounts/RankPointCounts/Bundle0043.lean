import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0041
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrameLA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.NGAnalytic.MassDataLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inst

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev anY : AnIn :=
  anOf (Y.tO u u') (Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
    ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
      ((locOf X u u' ψ).volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)))
    (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
    (Fintype.card (InfinitePlace X.B.I.F))
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq),
      KtopVOf X u u' Y.M Y.δ (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)⟩

def FrameVolAt : Prop :=
  (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).unitLevelVolume / (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).volZZ =
    (2 * D.host.v) ^ (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) *
      (X.B.g : ℝ) ^ (D.R.f * (D.R.rS + 1) * (2 * D.R.rS + 3))

theorem kapN_pos (hg : 0 < (X.B.g : ℝ)) : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  have hgS : 0 < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    unfold Formalism.MainNotions.S.Lat.gS
    first
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos D.host.g_prime.1.pos D.host.g_prime.2.pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).one_lt.le (D.host.g_prime 1).one_lt.le)
  positivity

theorem massDataValid_bk_of {large₂ : SizeData₂ D} {Cg cb Cw cT CT C0 C' Cl : ℝ} (hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u')
    (hrd : 0 < 2 * D.host.v) (hg : 0 < (X.B.g : ℝ)) (hT : MassDataTie X hb X0 ψ)
    (hLS : InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hMs : InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hCol : InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hInd : InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hVol : InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hKpp : KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hTy : InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hPC : ProdConv X u u' ψ) (hPr : PrimX X u) (hPr' : PrimX X u') (hKap : KapX X u u')
    (hNu : Formalism.L2.SG.RealObj.InNuX X u u' 1) (hInf : Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Pos)
    (hFV : FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) :
    ∃ Irat Ire : ℝ, MassDataAdmissible X Y u u' (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire := by
  obtain ⟨hM, hψ, hStd, hMC, hLC, -, hdet⟩ := hT
  have hH : HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hM, hc.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  have hk := kapN_pos X hg
  have hDst : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Dstar = DstC X :=
    Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq
      (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hH hKpp
  set B := bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hB
  have hCoo : 0 ≤ Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
    unfold Formalism.L2.SG.RealObj.DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hdeg : 0 < B.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hPos
    exact h
  have hNI : PN.NormInputs B := by
    refine ⟨hPos, rfl, ?_, ?_, ?_, hLS hH, hMs hH, hCol hH, ?_, ?_, hInd hH⟩
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 =
        Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 *
          (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)
      unfold Formalism.L2.SG.RealObj.IntOO Formalism.L2.SG.RealObj.IntC
      rw [hNu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCoo]
      field_simp
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 ≤ 1 / Formalism.L2.SG.RealObj.degX X
      have hd : 0 < Formalism.L2.SG.RealObj.degX X := hdeg
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hInf.2.2
    · exact inVolumes_of_compat X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ)
        (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hVol hH ⟨ψ, hψ, hStd, hMC⟩ hdet
    · exact inOrdinary_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq hPC
    · exact hTy hH hPC (locTieX_of X ψ u (hLC u) hPr) (locTieX_of X ψ u' (hLC u') hPr')
        (typFacts_of X u u' (Formalism.L2.SG.Pf.gSplitX_holds X) (tCongX X u u') hKap)
  have hLam : 0 < PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
      (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) := by
    unfold PN.abelian₂
    exact mul_pos (pow_pos hrd _) (Real.rpow_pos_of_pos hrd _)
  refine ⟨(B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)),
    (B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)) /
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
        (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)), ?_, ?_, hNI, ?_⟩
  · exact Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq Y
  · show B.d * B.d' / B.Dstar = duC X Y u * duC X Y u' / DstC X
    rw [hDst]
    rfl
  · have hL1 : PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f ≠ 0 := by
      unfold PN.abelian₂; exact (pow_pos hrd _).ne'
    have hL2 : (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos hrd _).ne'
    refine ⟨hrd, hg, hFV, ?_, ?_⟩
    · field_simp
    · field_simp

end Inst

section Closed

def pairSys0 {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ :=
  ⟨Empty, Empty.elim, Empty.elim, fun p => p.elim, fun p => p.elim, fun _ => False⟩

def idx0 (D : D7) : Fin D.R.k := ⟨0, by have := D.R.m_add_three_le_k; omega⟩

abbrev bk0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    S3.MassData (TypX X) :=
  bk X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

abbrev canonicalAnalyticData {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : AnIn :=
  anY X Y u u' ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

def OnTied (P : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I → Full X → D.what₂.Word → D.what₂.Word →
    (Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) → AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ → Prop) : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → P D X hb Y u u' X0 ψ

theorem stepChoiceDataC_of
    (hLS : OnTied fun _ X hb Y u u' X0 ψ =>
      InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hMs : OnTied fun _ X hb Y u u' X0 ψ =>
      InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hCol : OnTied fun _ X hb Y u u' X0 ψ =>
      InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hInd : OnTied fun _ X hb Y u u' X0 ψ =>
      InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hVol : OnTied fun _ X hb Y u u' X0 ψ =>
      InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hKpp : OnTied fun _ X hb Y u u' X0 ψ =>
      KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hTy : OnTied fun D X hb Y u u' X0 ψ =>
      InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
        (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0))
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hPr : OnTied fun _ X _ _ u u' _ _ => PrimX X u ∧ PrimX X u')
    (hKap : OnTied fun _ X _ _ u u' _ _ => KapX X u u')
    (hNu : OnTied fun _ X _ _ u u' _ _ => Formalism.L2.SG.RealObj.InNuX X u u' 1 ∧ Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos)
    (hFV : OnTied fun D X hb Y u u' X0 ψ =>
      FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
        (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)) :
    StepChoiceConstantsC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, _, _, C'₀, Cl₀, hsz⟩ := Formalism.L2.SG.NGCut.sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ hT => ?_⟩
  have hS := hsz C' Cl h1 h2 D large₂ X Y u u' hc
  unfold SizesRec at hS
  obtain ⟨_, _, hrd, _, hg1, _⟩ := hS
  have hg : 0 < (X.B.g : ℝ) := lt_of_lt_of_le one_pos hg1
  refine ⟨0, 0, 1, X.Fu u, Y.what₂ u, fun _ => 0, pairSys0 u u' (X.Fu u) (Y.what₂ u), fun _ => idx0 D,
    fun _ => idx0 D, fun _ => 0, ?_⟩
  exact massDataValid_bk_of X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
    (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) hc hrd hg hT
    (hLS Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hMs Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hCol Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hInd Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hVol Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hKpp Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hTy Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT)
    (hPC Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hPr Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).1 (hPr Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).2 (hKap Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hNu Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).1 (hNu Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).2
    (hPos Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hFV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT)

end Closed

end Formalism.L2.SG.NGAnalytic.MassDataLemmas
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def CohLp : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ⇑(φ' p) '' (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f' ≠
      (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F'₂)}.Finite

def CohIota : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ g, (Zd.M p).split = some g →
      Prod.map ⇑(φ' p) ⇑(LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
          (locH Zd p).iotaGraph g (tLoc Zd p γ) =
        (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

variable {u u' F0 what₂}

theorem cohResp_of (hLp : CohLp Zd u u' F0 what₂) (hIo : CohIota Zd u u' F0 what₂) : CohResp Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  refine ((hLp hP γ Z F'₂ φ' hH).union (hIo hP γ Z F'₂ φ' hH)).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, ne_eq] at hn
  obtain ⟨h3, h5⟩ := hn
  apply hp
  refine ⟨?_, ?_, h3, (hH.2.2.2 p).2.2.2.2.2, h5⟩
  · exact Set.image_id _
  · intro x x₂ hx hx₂
    rw [one_smul, one_smul]
    show (locH Zd p).mkW _ x = (locH Zd p).mkW _ x₂
    exact congrArg _ (Subtype.ext (hx.trans hx₂.symm))

theorem starCoh_of_P' (hGen : CohGen Zd u u' F0 what₂) (hLp : CohLp Zd u u' F0 what₂) (hIo : CohIota Zd u u' F0 what₂)
    (hGood : CohGood Zd u u' F0 what₂) : CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  starCoh_of_P Zd hGen (cohResp_of Zd hLp hIo) hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrame
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gram_fvec_zero {r : ℕ} {T : E} (F : FlagG S r T) :
    ∀ i j, (i ≠ Fin.last r ∨ j ≠ Fin.last r) → gram S F.fvec F.fvec i j = 0 := by
  intro i j hij
  have hfe : ∀ a : Fin r, F.fvec (Fin.castSucc a) = F.e a := fun a => by simp [FlagG.fvec]
  have hfz : F.fvec (Fin.last r) = F.z := by simp [FlagG.fvec]
  simp only [gram]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp at hij
    | cast b =>
      rw [hfz, hfe, ← LinearMap.IsSymm.eq_iff S.herm]
      exact F.z_orth b
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [hfz, hfe]; exact F.z_orth a
    | cast b => rw [hfe, hfe]; exact F.e_iso a b

theorem gram_fvec_last {r : ℕ} {T : E} (F : FlagG S r T) :
    gram S F.fvec F.fvec (Fin.last r) (Fin.last r) = -T := by
  simp only [gram, FlagG.fvec, Fin.snoc_last]
  exact F.z_norm

theorem comb_frame {r : ℕ} {T : E} (F : FlagG S r T) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hA : ∀ a b, b < a → A a b = 0) (hA1 : ∀ a, A a a = 1) :
    (∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (comb S F.fvec A a) (comb S F.fvec A b) = 0) ∧
      S.hT (comb S F.fvec A (Fin.last r)) (comb S F.fvec A (Fin.last r)) = -T := by
  have hg : ∀ a b, S.hT (comb S F.fvec A a) (comb S F.fvec A b) =
      star (A (Fin.last r) a) * (-T) * A (Fin.last r) b := by
    intro a b
    have e := congrFun (congrFun (show gram S (comb S F.fvec A) (comb S F.fvec A) = Aᴴ * (gram S F.fvec F.fvec * A) by
      rw [gram_comb_right, gram_comb_left]) a) b
    simp only [gram] at e
    rw [e, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r), gram_fvec_last, Matrix.conjTranspose_apply, mul_assoc]
      · intro c _ hc; rw [gram_fvec_zero F _ _ (Or.inr hc), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hc
      rw [Matrix.mul_apply, Finset.sum_eq_zero fun d _ => by rw [gram_fvec_zero F _ _ (Or.inl hc), zero_mul], mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hl : ∀ a, a ≠ Fin.last r → A (Fin.last r) a = 0 := fun a ha => hA _ _ (Fin.lt_last_iff_ne_last.2 ha)
  refine ⟨fun a b hab => ?_, ?_⟩
  · rw [hg]
    rcases hab with h | h
    · rw [hl a h, star_zero, zero_mul, zero_mul]
    · rw [hl b h, mul_zero]
  · rw [hg, hA1, star_one, one_mul, mul_one]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem star_frame_orthogonal (γ : TermDef.Term D u u' F0 what₂) :
    (∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (starFrame γ a) (starFrame γ b) = 0) ∧
      (VS D).hT (starFrame γ (Fin.last D.R.rS)) (starFrame γ (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  exact FsLA.comb_frame (repF γ).fl
    (fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E))
    (fun a b h => by simp [hξ1 a b h]) (fun a => by simp [hξ2 a])

variable (u u' F0 what₂)

def StarMinors : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    Z.det ≠ 0 ∧ (starZh (frame (lf D F0)) (starFrame γ)).det ≠ 0 ∧
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS * Z.det =
        leadMinorE Z D.R.rS * (starZh (frame (lf D F0)) (starFrame γ)).det

variable {u u' F0 what₂}

theorem starFrame_of (hM : StarMinors u u' F0 what₂) : StarFrame u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨hZ, hZ₁, hx⟩ := hM γ Z hC
  obtain ⟨h1, h2⟩ := star_frame_orthogonal γ
  obtain ⟨F₂, hZh, hom, -⟩ := FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx
  refine ⟨⟨F₂, F₂.z⟩, hZh, ?_, ?_⟩
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z := hZh
    rw [e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    exact hx
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z := hZh
    rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]
    exact hom

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmDetPf
section
noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP OmL

namespace OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem mat_frameAct {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (frameAct (frame F') ξ b)) =
      Zhat F0 F'.fl * ξ.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b

theorem map_det_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm

theorem det_ne_of_unit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0 := by
  intro h0
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul] at h
  exact not_isUnit_zero h

theorem gdl_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (l : ℕ) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl F0.fvec F'.fvec l = Formalism.MainNotions.S.Dl F0 F' l := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs <;> rfl

end OmD

open OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem modeMatrixDet_eq_adjointDet : OmDet Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS F' hP
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  have hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0 := by
    have h1 := det_ne_of_unit Zd p F0
      (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ
    rw [mat_frameAct, Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  refine ⟨hdγ, fun hZ => ?_⟩
  have hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  have hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0 := by
    rw [dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]
  have hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS *
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) =
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS *
        (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) := hT2.2.2.2.1.2.2.2.2.2
  rw [hD2, mul_zero] at hId
  obtain ⟨uγ, huγ⟩ := hT2.1.1.2.2.2.1
  rw [← huγ] at hId
  have hDr := (Units.mul_left_eq_zero uγ).1 hId.symm
  have e := Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p)
    (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)
  rw [show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e] at hDr
  have hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj
      (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i))) :=
    IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _
  have hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i)) :=
    IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _
  have hg := (hu1.mul hu2).mul_right_eq_zero.1 hDr
  rw [map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq] at hg
  have hG := hP.1.1.2.2
  rw [fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm)] at hG
  apply hG
  show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0
  unfold Formalism.MainNotions.S.Gflag
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]
  simp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end


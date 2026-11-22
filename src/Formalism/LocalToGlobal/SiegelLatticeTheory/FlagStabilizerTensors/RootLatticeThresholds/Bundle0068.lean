import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0067
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0063
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinJF
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.AmpWinJF

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

def wt {u u' : D.what₂.Word} (t : D.s.Term u u') : Point D.host.E (D.R.rS + 1) := Formalism.L2.SG.PairVal.ptOf (tc hI t)

def AmpPt (ν : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    hsNormSq (JtOf hI t) = Formalism.L2.SG.LoopTerm.volRC hI t ^ 2 *
      (Formalism.L2.SG.Pf.OOCore3.sclV Y u u' * hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν (wt hI t)))

def PtFacts : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    (∃ g, IsPtRep X u u' (wt hI t) g) ∧ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' (wt hI t)) v

def LocUniqT (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.LoopTerm.nu1 hI C t τ) (Formalism.L2.SG.LoopTerm.gamR hI C t τ)) =
      hsNormSq ((locS hB u u' τ).J ((νl (wt hI t) (vOf X τ)).map
        (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' (wt hI t)) (vOf X τ))))
        (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (wt hI t) τ))

end Defs

section Main

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

end Main

section Pts

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) (u u' : D.what₂.Word)

end Pts

section Pin

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

theorem levelVolume_pos : 0 < X.volK2 := by
  have h := Formalism.L2.SG.Closed.level_subgroup_properties X
  exact ENNReal.toReal_pos h.2.2.1.ne' h.2.2.2.ne

end Pin

end Formalism.L2.SG.Pf.AmpWinJF
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCell
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem cj_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) :
    cj k r κ τ h = h := by
  ext i j
  rw [cj_apply]
  by_cases h0 : h i j = 0
  · rw [h0, mul_zero]
  · have e := fix_gen (fun i => ((tV k r κ τ i : ℝ) : ℂ)) 1 (fun i h1 h2 => by simp [tV_wb i h1 h2]) hh.1 hh.2.1 i j h0
    have e' : tV k r κ τ i = tV k r κ τ j := by exact_mod_cast e
    rw [e', inv_mul_cancel₀ (tV_pos hκ hτ j).ne']
    simp

theorem map_cjT_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)}
    (h : IsHaarOn (UWset k r z) μ) : μ.map (cjT k r κ τ) = μ := by
  have hae : cjT k r κ τ =ᵐ[μ] id := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) h.2.2.1
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro hU
    apply hx
    funext i j
    show cj k r κ τ (Matrix.of x) i j = x i j
    rw [cj_UW hκ hτ hU]; rfl
  rw [Measure.map_congr hae, Measure.map_id]

theorem haarProb_unique {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn (UWset k r z) μ) (hμ1 : μ Set.univ = 1) (hν : IsHaarOn (UWset k r z) ν) (hν1 : ν Set.univ = 1) :
    μ = ν := by
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  have hC := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hK := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT
  have fin : ∀ (m : Measure (Mt k r)), m Set.univ = 1 → ∀ K : Set (Mt k r), IsCompact K → m K < ⊤ :=
    fun m hm K _ => (measure_mono (Set.subset_univ K)).trans_lt (by rw [hm]; exact ENNReal.one_lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 μ hC h0 hμ.2.2.1 hμ.2.2.2 (fin μ hμ1)
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 ν hC h0 hν.2.2.1 hν.2.2.2 (fin ν hν1)
  have hfin : μ0 Set.univ ≠ ⊤ := by
    have hle := measure_univ_le_add_compl (μ := μ0) (UWset k r z : Set (Mt k r))
    have hc0 : μ0 (UWset k r z : Set (Mt k r))ᶜ < ⊤ := (le_of_eq h0.conc).trans_lt ENNReal.zero_lt_top
    exact (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨h0.finite_compact _ hK, hc0⟩)).ne
  have hne : μ0 Set.univ ≠ 0 := by
    intro h; apply h0.ne_zero; rw [← Measure.measure_univ_eq_zero]; exact h
  have e1 : (c : ENNReal) * μ0 Set.univ = 1 := by rw [← hμ1, hc]; rfl
  have e2 : (d : ENNReal) * μ0 Set.univ = 1 := by rw [← hν1, hd]; rfl
  have hcd : (c : ENNReal) = d := by
    have := e1.trans e2.symm
    exact (ENNReal.mul_left_inj hne hfin).mp this
  rw [hc, hd, ENNReal.coe_injective hcd]

section Choice

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem muWc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ))
    (hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1) := by
  rw [map_cjT_UW (inv_pos.mpr (kaB_pos D)) one_pos (C.muW_haar u τ)]
  show (μW_exists X C u (vOf X τ)).choose = _
  obtain ⟨h1, h2⟩ := (μW_exists X C u (vOf X τ)).choose_spec
  generalize (μW_exists X C u (vOf X τ)).choose = m at h1 h2 ⊢
  have hS : UWset D.R.k D.R.rS (zc X C u (vOf X τ)) = UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [zc_vOf_eq_zB_of_inWb C u u τ hz, UWset_smul one_pos]
  rw [hS] at h1
  exact haarProb_unique hz hT h1 h2 (C.muW_haar u τ) (C.muW_one u τ)

end Choice

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsHaarOn (RStab D.R.k D.R.rS (gB C τ γ)) (muRB C τ μRv)

def QuotTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsQuotLoc μRv ν →
    PI.BesselPeriodGGP.IsQuotMeas (locW C u u' τ).μG
      ((muRB C τ μRv).map (fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j))
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ))

def PinHypAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
    (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
  IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
    μRv ∧ IsQuotLoc μRv ν

def CutAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
          (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (fcAt C u u' τ a b ξ ξ' c) p) (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).μSS

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gap

def GapEv {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ y : ℝ, ∀ x, y ≤ x → ∀ i : Fm.Ix x, Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)

def CG (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ GapEv Fm

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def selG : SSel (CG 𝒞) := fun Fm h => sel Fm h.1

def yFG : ∀ {eps : ℝ} (Fm : FamP eps), CG 𝒞 Fm → ℝ := fun _ h => Classical.choose h.2

theorem gap_of {eps : ℝ} {Fm : FamP eps} (h : CG 𝒞 Fm) {x : ℝ} (hx : yFG Fm h ≤ x) (i : Fm.Ix x) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
  Classical.choose_spec h.2 x hx i

theorem hyFG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) : YFOK (selG sel) yFG := by
  intro eps Fm hc x hx h0 hy i
  have hg := gap_of hc hy i
  exact ⟨hFX _ _ hg, (hWu _ hg _).1⟩

def CX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Formalism.L2.SG.LocWSOf.Choice X 1 :=
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  Classical.choice (Formalism.L2.SG.Pf.choiceExists X 1 one_pos)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def BG (hJ : PI.BesselMapUniq.BesselMapUniq) (C1f : List ℝ → ℝ) (hC1 : ∀ l, 0 ≤ C1f l) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (_ : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut) :=
  fun Fm hc x hx i u u' => Formalism.L2.SG.Pf.LoopLoc.loopLocDatOf
    (gap_of hc (hyR (selG sel) yFG hx) i) (Fm.ties x i).dsig_tie hJ
    (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
    (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) (hC1 _)) u u'

theorem closed_sub {𝒞' : FamClass} (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm)
    {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) : Closed 𝒞' P := by
  obtain ⟨e, he, H⟩ := h
  exact ⟨e, he, fun eps h1 h2 => by
    obtain ⟨K, hK⟩ := H eps h1 h2
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩⟩

variable (C0 : ℝ)

theorem loopRowS_of_sub (hG : Closed 𝒞 fun Fm _ => 𝒞 Fm → GapEv Fm) (h : LoopRowS C0 (CG 𝒞) (selG sel)) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  obtain ⟨e1, he1, H1⟩ := h aF
  obtain ⟨e2, he2, H2⟩ := hG
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  refine ⟨K1.sup K2, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  intro hc'
  have hg := hK2 Fm CH hc hL2 hc'
  exact hK1 Fm CH ⟨hc', hg⟩ hL1 ⟨hc', hg⟩

end Gap

section PartC

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def RMeasExAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (u u' : D.what₂.Word),
    (∀ τ, GoodW D τ u u' 1 (Formalism.L2.SG.LocWSOf.locW C u u' τ)) → LoopTerm.RMeasEx hI C u u'

def JFactNAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (hB : Formalism.L2.SG.LocWSOf.WuBessel C) (u u' : D.what₂.Word),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → LoopTerm.JFactN hI C hB u u'

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

def MG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hJ : PI.BesselMapUniq.BesselMapUniq)
    (hRM : RMeasExAll) (hJF : JFactNAll) (hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (hx : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR (selG sel) yFG (hyFG sel hFX hWu) Fm hc x hx i) u u' ((fun _ => 1) Fm.cOut)
        (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u') :=
  fun Fm hc x hx i u u' =>
    LoopTerm.loopTermOfN (wOf ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X)
      (((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).hI
        (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (hvOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (Fm.L x i) 1 (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
      (Formalism.L2.SG.Pf.LoopLoc.wuBessel_of (gap_of hc (hyR (selG sel) yFG hx) i) hJ _) u u'
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)
      (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW
      (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodS
      (hRM _ _ _ _ _ _ u u' (BG sel hJ (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW)
      (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u') (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u')
      (hJF _ _ _ _ _ _ _ u u' (gap_of hc (hyR (selG sel) yFG hx) i))
      (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos _ u u')
      (Formalism.L2.SG.Pf.LoopBCovN.covWinN_sizes hCF _ (Fm.L x i) (Fm.sizes x (raise_lt hx) i) (by norm_num) u u')
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)

variable (C0 : ℝ)

end PartC

end Formalism.L2.SG.LoopsTies
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChainG
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR
  Formalism.L2.SG.ThmBUseR Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChainG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem jointAmplitudeRotated_generic (Y : Full X) (u : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExPR u u C) (hM : RMeasExP u u C) (hP : LocalAmplitudesPositive Y u u ν C hB) (hT : ThetaWinP Y u u ν C hB large₂ C1) :
    JointAmplitudeFactorizationRotated (genT (Y.tO u u)) (NOfG Y u νL ν ng) large₂ C1 (WX C u u) (AX hB u u) (D.mem u).A.T (D.mem u).A.T 1 := by
  intro γ w _ hw hb hJ
  subst hw
  have hJ' : 0 < J2of Y u u ν (toPts w) := hJ
  obtain ⟨w', hw', g0, hg0⟩ := isPtRep_of_J2of hJ'
  have hw'w : w' = w := toPts_injective hw'
  subst hw'w
  have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w' g := ⟨g0, hg0⟩
  have hP1 := hP w' hb hJ'
  set J2 := J2of Y u u ν (toPts w') with hJ2
  set th := thetaP u u hB J2 w' with hth
  have hthv : th = (localAmplitudeProduct u u hB w' / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    rw [hth]; unfold thetaP; rw [if_pos ⟨hJ', hP1⟩]
  have hth0 : 0 < th := by rw [hthv]; exact Real.rpow_pos_of_pos (div_pos hP1 hJ') _
  have hfc : (0 : ℝ) < 2 * Fintype.card D.what₂.Tau := by
    have := card_pos' D; positivity
  have hpow : th ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u hB w' / J2 := by
    rw [hthv, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hJ').le]
    push_cast
    rw [one_div_mul_cancel hfc.ne', Real.rpow_one]
  refine ⟨gamP C u u w', fun _ => th, fun τ => (ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ, fun τ => ?_, ?_⟩
  · have hnu : ∃ ν₁, RMeas D (locW C u u τ) (gamP C u u w' τ) 1 ν₁ := hM w' hb hrep τ
    have hnuP : nu1P C u u w' τ = hnu.choose := by unfold nu1P; rw [dif_pos hnu]
    refine ⟨hR w' hb hrep τ, hT w' hb hJ', ?_⟩
    obtain ⟨p, μR, hR1, hQ⟩ := hnu.choose_spec
    refine ⟨p, μR, hR1, ?_⟩
    show IsQuotMeas _ (ENNReal.ofReal th • μR) ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
    rw [hnuP]
    have hQ' : IsQuotMeas (WX C u u τ).μG μR hnu.choose := by
      simpa [ENNReal.ofReal_one, one_smul] using hQ
    exact Formalism.L2.SG.Pf.LTL.isQuotMeas_smul hQ' (by simpa using hth0) ENNReal.ofReal_ne_top
  · have hloc : ∀ τ, hsNormSq ((AX hB u u τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
        (gamP C u u w' τ)) = (th ^ 2)⁻¹ *
          hsNormSq ((locS hB u u τ).J (nu1P C u u w' τ) (gamP C u u w' τ)) := by
      intro τ
      rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hth0.le, Complex.normSq_ofReal]
      congr 1
      rw [sq, mul_inv]
    have hprod : ∏ τ, hsNormSq ((AX hB u u τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
        (gamP C u u w' τ)) = J2 := by
      rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      change ((th ^ 2)⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u hB w' = J2
      rw [inv_pow, ← pow_mul, hpow]
      field_simp
    have hnn : ∀ τ, 0 ≤ hsNormSq ((AX hB u u τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u w' τ)
        (gamP C u u w' τ)) := fun τ => Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
    rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_prod_of_nonneg (fun τ _ => hnn τ), hprod]
    exact le_rfl

theorem rowBDataGR_of_rest {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word}
    {ν : X.B.I.Ginf → Measure X.B.I.Ginf} {C1 Cn Ire : ℝ} (h : RowRestR large₂ Y u u ν C1 Cn Ire) :
    RowBDataGR large₂ Y u ν C1 Cn Ire := by
  obtain ⟨hIre, θ, C, hB, h0, hw, hl, hM, hP, hT, hN⟩ := h
  exact ⟨hIre, θ, C, hB, h0, hw, hl, 1, zero_le_one,
    fun νL ng => jointAmplitudeRotated_generic Y u large₂ C1 C hB ν νL ng (Formalism.L2.SG.Pf.RelPtR.relPtExPR_holds C u u) hM hP hT,
    fun sec hs => by rw [ENNReal.ofReal_one, one_mul]; exact hN sec hs⟩

theorem rowBDataUnifGR_of (h : RowRestUnifR) : RowBDataUnifGR := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, Cn, a, b, h2⟩ := h Cg cb Cw cT CT C0
  exact ⟨C1, Cn, a, b, fun C' Cl h1 h3 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp =>
    rowBDataGR_of_rest (h2 C' Cl h1 h3 D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp)⟩

end Formalism.L2.SG.Pf.ThmBChainG

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.ThmBChainG

theorem theoremB_generic_final (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hR : RowRestUnifR) : StepThmBG :=
  stepThmBG_ofR hB hA Formalism.L2.SG.PointUniformity.ptUnifG (rowBDataUnifGR_of hR)

end Formalism.L2.SG.Pf
end
end


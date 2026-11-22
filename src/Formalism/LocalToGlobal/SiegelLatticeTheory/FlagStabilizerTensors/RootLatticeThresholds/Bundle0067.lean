import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0055
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0056
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0066
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0062
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpOrbCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalAmpRoot
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
section
noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants
  Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec

namespace Formalism.L2.SG.Pf.AmpWinGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word)

def muNv (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) := muNl C (X.pl v) v

def muHv (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) := muHl C u (X.pl v) v

theorem place_all (hLF : LocFactor C) (hB : WuBessel C) (v : InfinitePlace X.B.I.F) :
    SigmaFinite (muNv C v) ∧ SigmaFinite (muHv C u v) ∧ QPK.InvOn (muNv C v) (Nloc X u v) ∧
      QPK.InvOn (muHv C u v) (Hloc X u v) ∧ muHv C u v Set.univ = 1 ∧
      QPK.mulMap (muNv C v) (muHv C u v) (QPK.prodSet (Nloc X u v) (Hloc X u v))ᶜ = 0 ∧
      ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNv C v) (muHv C u v)) = 1) ∧
        ∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
          l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v)) := by
  have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
      SigmaFinite (muNl C τ w) ∧ SigmaFinite (muHl C u τ w) ∧ QPK.InvOn (muNl C τ w) (Nloc X u w) ∧
      QPK.InvOn (muHl C u τ w) (Hloc X u w) ∧ muHl C u τ w Set.univ = 1 ∧
      QPK.mulMap (muNl C τ w) (muHl C u τ w) (QPK.prodSet (Nloc X u w) (Hloc X u w))ᶜ = 0 ∧
      ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        ∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) = l2SG (C.nuS u τ) (phiOf hB u τ) := by
    rintro τ w rfl
    have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
    have hH1 : muHl C u τ (vOf X τ) Set.univ = 1 := by
      have h : (muHl C u τ (vOf X τ)).map (eT C τ (vOf X τ)) Set.univ = C.muW u τ Set.univ := by
        rw [map_muHl C u τ]
      rw [Measure.map_apply (eT_emb C τ (vOf X τ)).measurable MeasurableSet.univ, Set.preimage_univ,
        C.muW_one u τ] at h
      exact h
    have hconc : QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))
        (QPK.prodSet (Nloc X u (vOf X τ)) (Hloc X u (vOf X τ)))ᶜ = 0 := by
      have hHH : Hloc X u (vOf X τ) = Hfix X u (vOf X τ) := Hloc_eq X u (vOf X τ)
      rw [hHH]
      exact (invOn_mulMap C u τ).2.2.1
    obtain ⟨β, hβm, hβ1, hid⟩ := loc_main C u τ hLF hB
    exact ⟨sf_muNl C τ hθ, sf_muHl C u τ, invOn_muNl C u τ, invOn_muHl C u τ, hH1, hconc, β, hβm, hβ1, hid⟩
  exact key (X.pl v) v (X.pl.symm_apply_apply v)

theorem map_trInf (hsf : ∀ v, SigmaFinite (muNv C v)) (hθ : 0 < θ) :
    MeasurableEmbedding (Formalism.L2.SG.LoopTerm.trInf C) ∧
      (Measure.pi (muNv C)).map (Formalism.L2.SG.LoopTerm.trInf C) = Formalism.L2.SG.LoopTerm.dnB D θ := by
  have hPemb : MeasurableEmbedding
      (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) :=
    (Topology.IsClosedEmbedding.piMap fun τ =>
      Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding
  have htr : Formalism.L2.SG.LoopTerm.trInf C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) :
      (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
    funext x τ
    rfl
  refine ⟨htr ▸ hPemb.comp (MeasurableEquiv.measurableEmbedding _), ?_⟩
  rw [htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]
  have h1 : (Measure.pi (muNv C)).map (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm =
      Measure.pi (fun τ => muNv C (X.pl.symm τ)) :=
    ((measurePreserving_piCongrLeft (muNv C) X.pl.symm).symm _).map_eq
  have h2 : (fun τ => muNv C (X.pl.symm τ)) = fun τ => muNl C τ (X.pl.symm τ) := by
    funext τ
    show muNl C (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muNl C τ (X.pl.symm τ)
    rw [Equiv.apply_symm_apply]
  rw [h1, h2]
  have hmap : ∀ τ, (muNl C τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = muNB D θ := fun τ => map_muNl C τ hθ
  have : ∀ τ, SigmaFinite ((muNl C τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ))) := fun τ => by
    rw [hmap τ]; exact (muNB_haar (D := D) hθ).1
  refine (Measure.pi_map_pi (μ := fun τ => muNl C τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ))
    (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_
  simp_rw [hmap]
  rfl

theorem massU_of (Y : Formalism.L2.SG.Full.Full X) (hLF : LocFactor C) (hB : WuBessel C) :
    Formalism.L2.SG.Pf.AmpWin.MassU Y u C hB := by
  have hθ : 0 < θ := by
    obtain ⟨τ⟩ := Formalism.L2.SG.LoopTerm.tau_nonempty D
    exact Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using place_all C u hLF hB

  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  have hpiH : Set.pi Set.univ (Hloc X u) = Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨k1, k2, k3, k4⟩ := X.muH_haar u
  have hHfix : ∀ v, Hloc X u v = Hfix X u v := fun v => Hloc_eq X u v
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨cH, hcH0, hcHt, hcH⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Hloc X u))
    (isClosed_set_pi fun v _ => by rw [hHfix]; exact (place_facts X u v).2.1.isClosed)
    (QPK.isGrp_pi _ fun v => by rw [hHfix]; exact (place_facts X u v).2.2.2.1)
    (X.muH u) (Measure.pi (muHv C u)) ⟨k1, k2, by rw [hpiH]; exact k3, by rw [hpiH]; exact k4⟩
    (QPK.invOn_pi _ _ hH)

  set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hF_def
  have hFm : ∀ v, Measurable (F v) := fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2
  have hFinv : ∀ v, ∀ m ∈ Nloc X u v, ∀ h ∈ Hloc X u v, ∀ x, F v (m * h * x) = F v x := by
    intro v m hm h hh x
    have hs := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
    show ‖X.Wloc u v (m * h * x)‖ₑ ^ 2 = ‖X.Wloc u v x‖ₑ ^ 2
    rw [← enorm_norm (X.Wloc u v (m * h * x)), norm_Wloc_inv X u v hs, enorm_norm]
  set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hf_def
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := X.nuQ_weil u f hfm
  have hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * F v y ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
    QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
      (cN * cH) * ∏ v, F v (x v) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      hcN, hcH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have e1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf,
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [e1]
    rw [QPK.lintegral_pi_prod_mul (muNv C) (muHv C u) (fun v z => β v (z * x v) * F v (z * x v))
      (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]
    have e2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (muNv C v) (muHv C u v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(QPK.mulMap (muNv C v) (muHv C u v)), s ∈ QPK.prodSet (Nloc X u v) (Hloc X u v) :=
        mem_ae_iff.mpr (hconc v)
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        simp only [hFinv v m hm h hh])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [e2]
    ring
  simp_rw [hin] at key
  have hPm : Measurable (fun x : X.B.I.Ginf => ∏ v, F v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hFm v).comp (measurable_pi_apply v)
  rw [lintegral_const_mul _ hPm, hL1] at key
  have hW1 : ∫⁻ x, ∏ v, F v (x v) ∂(X.nuQ u) = 1 := by
    rw [← (X.Wu_spec u).2.2.2.2]
    refine lintegral_congr fun x => ?_
    rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]
  rw [hW1, mul_one] at key

  have hprod : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = cN * cH := by
    rw [← key]
    refine (Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) _
      (fun v => rfl)).symm.trans ?_
    exact Finset.prod_congr rfl fun v _ => (hloc v).symm

  obtain ⟨hemb, hmapT⟩ := map_trInf C (fun v => hsfN v) hθ
  have hcov : Measure.pi (muNv C) (Y.FN u) =
      Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hNF : X.muN u (Y.FN u) = cN * Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) := by
    rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]
  have hHU : X.muH u Set.univ = cH := by
    rw [hcH, Measure.smul_apply, smul_eq_mul, ← Set.pi_univ, Measure.pi_pi]
    rw [Finset.prod_eq_one fun v _ => hH1 v, mul_one]
  unfold Formalism.L2.SG.Pf.AmpWin.MassU Formalism.L2.SG.LoopTerm.covN
  rw [hNF, hHU, ← ENNReal.toReal_prod, hprod, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

theorem ampWin_of_loc (Y : Formalism.L2.SG.Full.Full X) (u' : D.what₂.Word) (hLF : LocFactor C) (hB : WuBessel C) :
    Formalism.L2.SG.Pf.AmpWin.AmpWinP Y u u' C hB :=
  Formalism.L2.SG.Pf.AmpWin.ampWin_of Y u u' C hB (massU_of C u Y hLF hB) (massU_of C u' Y hLF hB)
    (fun τ => Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ) (fun τ => Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ)

theorem K0_mem_covWin_of_locFactor_wuBessel (Y : Formalism.L2.SG.Full.Full X) (u' : D.what₂.Word) (hLF : LocFactor C) (hB : WuBessel C)
    (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB ∧
      Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  have hA := ampWin_of_loc C u Y u' hLF hB
  exact ⟨Formalism.L2.SG.Pf.AmpWin.minWeight_pos Y u u' C hB hA hV hc, Formalism.L2.SG.Pf.AmpWin.K0_mem_covWin_of_ampWin Y u u' C hB hA hV hW⟩

end Formalism.L2.SG.Pf.AmpWinGlob
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmplitudeBoundsAllChoicesUniform
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.Pf.OOCore3 Formalism.L2.SG.Pf.LocNorm
  Formalism.L2.SG.Pf.ThmBChain5
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AmplitudeBoundsAllChoices {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ θ : ℝ, 0 < θ ∧ normWin D large₂ C1 θ ∧ ∀ (C : Choice X θ) (hB : WuBessel C),
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocUniqP u u' C hB νl) ∧
    0 < K0 Y u u' C hB ∧ WinK large₂ C1 (K0 Y u u' C hB) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def AmplitudeBoundsAllChoicesUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → AmplitudeBoundsAllChoices large₂ Y u u' ν C1 Cn Ire

def DsigOfCtx : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → Formalism.BasicNotions.dsigTie D

end Formalism.L2.SG.Pf.ThmBChain6
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinAt
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def fcAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (g : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) :
    X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ) :=
  Formalism.L2.SG.Pf.CarrierT.coef0 X C u u' τ a b ξ ξ' c
    (torS (muT D) D.R.k D.R.rS * g * torS (muT D)⁻¹ D.R.k D.R.rS)

theorem gStd_eq (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := by
  unfold Qc Qic Qcs Qics
  rw [pl_vOf, ← torS_conj]
  simp only [gB, trG, Matrix.mul_assoc]

theorem measurable_trG {τ : D.what₂.Tau} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (h2 : Q * Qi = 1) :
    Measurable (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (trG Q Qi γ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
  (Formalism.L2.SG.Pf.WuBL.trG_closedEmb' (Formalism.L2.SG.Pf.Choice.n_eq' X) _ h2).measurable

theorem muStd_eq (τ : D.what₂.Tau) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    muStd (kaB D) (muRB C τ μRv) =
      μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)) := by
  have hQ := (C.isT τ).2.1
  have hQc : Qc X C (vOf X τ) * Qic X C (vOf X τ) = 1 := (transpC X C (vOf X τ)).2.1
  unfold muStd muRB
  rw [← cAE_coe, ← cjE_coe (inv_pos.mpr (kaB_pos D)) one_pos,
    Measure.map_map (cAE D.R.k D.R.rS).measurable (measurable_trG hQ),
    Measure.map_map (cjE (k := D.R.k) (r := D.R.rS) (inv_pos.mpr (kaB_pos D)) one_pos).measurable
      ((cAE D.R.k D.R.rS).measurable.comp (measurable_trG hQ))]
  congr 1
  funext x
  show cjT D.R.k D.R.rS (kaB D)⁻¹ 1 (cA D.R.k D.R.rS (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x))) = _
  funext i j
  show cj D.R.k D.R.rS (kaB D)⁻¹ 1 (Matrix.of (cA D.R.k D.R.rS (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x)))) i j = _
  rw [of_cA, ← gStd_eq C τ x]
  rfl

theorem fcAt_eq (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) :
    fcAt C u u' τ a b ξ ξ' c = fun g => c • stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') g := by
  funext g
  unfold fcAt Formalism.L2.SG.Pf.CarrierT.coef0
  rw [torS_conjI]
  rfl

theorem lamPl_ne (cO : ℝ) (scl κ : ℂ) (D : D7) (θ : ℝ) (κ₀ : ENNReal) (hcO : cO ≠ 0) (hscl : scl ≠ 0) (hκ : κ ≠ 0)
    (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hk0 : kapN D θ ≠ 0) : lamPl cO scl κ D θ κ₀ ≠ 0 := by
  unfold lamPl
  have hs := tN_toReal_ne D θ κ₀ h0 h1 hk0
  refine inv_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) hscl) hκ) ?_)
  · exact_mod_cast hcO
  · exact_mod_cast hs

theorem pinAt (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hc0 : c ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (hAmp : ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν = κ • (locS hB u u' τ).J νR γ)
    (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hN : Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS = haarLie (Nset D.R.k D.R.rS) κ₀)
    (hWc : μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hWc' : μWc X C u' (vOf X τ) = (C.muW u' τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hcO : cOf hB u τ ≠ 0) (hscl : sclOf hB u u' τ ≠ 0)
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (νB : Measure (PairSp D.R.k D.R.rS))
    (hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB)
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)))
    (hcut : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ))
        (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ) (fcAt C u u' τ a b ξ ξ' c) p)
        (baseOf X C u u' (vOf X τ)).μSS) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) •
        Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
          (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
          (fcAt C u u' τ a b ξ ξ' c) := by
  have hk0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have hl := lamPl_ne (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ hcO hscl hκ h0 h1 hk0
  rw [fcAt_eq C hB u u' τ hW hA hT hT' a b ξ ξ' c] at hcut ⊢
  rw [← gStd_eq C τ γ, ← muStd_eq C τ μRv] at hcut ⊢
  obtain ⟨θ', hθ', hint⟩ := hcut
  have hcut' : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (muStd (kaB D) (muRB C τ μRv)) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D)
          (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) p)
        (baseOf X C u u' (vOf X τ)).μSS := by
    refine ⟨θ', hθ', ?_⟩
    have h : Integrable (c • (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
          (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D)
            (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) p)) (baseOf X C u u' (vOf X τ)).μSS := by
      refine hint.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (congrArg (fun Y => θ' p • Y) (Formalism.L2.SG.Pf.Carrier.CarPin.orbIntegrand_smul (baseOf X C u u' (vOf X τ))
        (gStd (kaB D) (gB C τ γ)) (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
          (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) c p)).trans (smul_comm _ _ _)
    exact (integrable_smul_iff hc0 _).mp h
  have hP := pinPlace C hB u u' τ hW hA hT hT' _ κ hAmp κ₀ h0 h1 hN hWc hWc' γ μRv ν νB hcell hG hcut'
  have hS := Formalism.L2.SG.Pf.Carrier.CarPin.orbJ_smulF (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
    (muStd (kaB D) (muRB C τ μRv)) (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) hc0
  refine Eq.trans ?_ (congrArg (fun Y => (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) • Y) hS.symm)
  refine Eq.trans ?_ (congrArg (fun Y => (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) • c • Y) hP.symm)
  have key : ∀ (a b d : ℂ) (Y : X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)), a • b • d • Y = (a * b * d) • Y :=
    fun a b d Y => by rw [smul_smul, smul_smul]
  refine Eq.trans ?_ (key _ _ _ _).symm
  have e1 : lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹ * c * (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀)⁻¹
      = 1 := by field_simp
  rw [e1, one_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopLocPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LoopLoc

variable {D : D7}

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem wuBessel_of {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hJ : PI.BesselMapUniq.BesselMapUniq) (C : Choice X θ) : WuBessel C :=
  Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_of_jsz hJ)
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def loopLocDatOf (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (hT : Formalism.BasicNotions.dsigTie D)
    (hJ : PI.BesselMapUniq.BesselMapUniq) {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) {large₂ : SizeData₂ D} {C1 : ℝ}
    (hwin : normWin D large₂ C1 θ) (u u' : D.what₂.Word) : Formalism.L2.SG.LoopTieOf.LoopLocDat D large₂ u u' C1 where
  θ := θ
  θ_win := hwin
  W τ := locW C u u' τ
  goodW τ := goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ)
    (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)
  A τ := locS (wuBessel_of hG hJ C) u u' τ
  goodS τ := goodS_of (wuBessel_of hG hJ C) u u' τ (Formalism.L2.SG.Pf.goodSRest_all hG hT (wuBessel_of hG hJ C) u u' τ)
  deg_eq τ := deg_eq (wuBessel_of hG hJ C) u u' τ

end Formalism.L2.SG.Pf.LoopLoc
end
end


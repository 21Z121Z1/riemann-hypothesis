import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0039
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairTiesPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0049
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0047

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsCountBase
section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsCountBase

open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

open Formalism.MainNotions.BridgeLemma NumberField in
theorem splits_X (k : Fin 2) : SplitsCompl X.B.I.E (D.host.g k) := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  exact Formalism.L2.SG.ThmSOwn.splitsCompl_of_equiv X.ιE hspl

theorem hc_X (hT : AutTie D X.B X.pl) (v : NumberField.InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  exact Inh.aut_isHCParam_of_autTie hT v

theorem countBase_of (hT : AutTie D X.B X.pl) {large₂ : SizeData₂ D} {n0 : ℕ} {A C cb : ℝ}
    (hp : AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n0 A C cb) (hg1 : 4 * D.R.r < D.host.g 1) : CountBase X n0 A C cb := by
  obtain ⟨-, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, p12⟩ := hp
  have hn := hT.n_eq
  have hf := hT.f_eq
  have hrd := hT.rd_eq
  have tg := X.g_eq
  have hq : ∀ v, X.B.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.B.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := hT.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  refine ⟨large₂.sc.b, C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE), fun k => ?_,
    fun v a c hac => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, hc_X X hT, ?_, ?_, ?_, D.host.g_prime _, ?_, splits_X X _⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [hrd, hn]; exact p4
    · intro v a
      rw [hT.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [hn]
      fin_cases k
      · exact hg1
      · exact p7
  · rw [hT.lam_eq v a, hT.lam_eq v c]
    exact p9 _ _ _ (by rw [← hT.eps_eq v a, ← hT.eps_eq v c]; exact hac)
  · rw [hn, hf, hrd]
  · rw [hf, hn]; exact p10
  · rw [hf, hn]; exact p12
  · have h := Formalism.MainNotions.BridgeLemma.Dstar_pos D
    rw [hT.Dstar_eq] at h
    exact h

theorem countBase_of_hyp (hT : AutTie D X.B X.pl) {L : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} {n0 : ℕ}
    {A C cb7 : ℝ} (hC : 0 ≤ C) (hcb : 0 < cb7) (hA : 2 * Cg ≤ A) (hn0 : (n0 : ℝ) ≤ D.R.k) (hCl2 : 2 ≤ Cl)
    (hCl3 : 2 * C ≤ Cl) (hll : Real.log L.sc.L ≤ cb7 * D.R.k) (hh : AdmissibleBoundsFromSource.hyp D L C0 C' Cl Cg cb Cu cT CT) :
    CountBase X n0 A C cb7 := by
  have hp := count_parameters_of_hyp L C0 C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hh
  refine countBase_of X hT hp ?_
  obtain ⟨-, hH, -⟩ := hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ContinuousCyclotomicCharacter₂, -⟩ := hH
  have hk5 := Formalism.MainNotions.S.five_le_k (D := D)
  have hb2 := Formalism.MainNotions.S.two_le_scb L
  have h5 : (4 : ℝ) * D.R.r < D.host.g 1 := Formalism.MainNotions.S.four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) Formalism.MainNotions.S.r_le_two_k ContinuousCyclotomicCharacter₂
  exact_mod_cast h5

section Fam

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData Formalism.L2.SG.ThmSOwn

variable {eps : ℝ} (Fm : FamP eps)

theorem countBaseOwn (C0 : ℝ) (n0 : ℕ) (A C cb7 : ℝ) (hC : 0 ≤ C) (hcb : 0 < cb7)
    (hA : 2 * (Fm.CYL + 1) ≤ A) (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm) :
    HypOwn Fm C0 fun D L => ∀ X : HidaSetting D, AutTie D X.B X.pl → CountBase X n0 A C cb7 := by
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) n0 (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually (cb7 * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  refine ⟨max (Fm.x1 + 1) x4, fun x hx i hh X hT => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hx
    linarith
  have hy := hx4 x (le_trans (le_max_right _ _) hx)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hL := scL_eq Fm x hx1 i
  have hk8 := k_ge_of_hyp (Fm.L x i) hh
  rw [hL, Fm.CGam_eq x i] at hk8
  refine countBase_of_hyp X hT hC hcb hA ?_ hCl2 hCl3 ?_ hh
  · have : (n0 : ℝ) ≤ n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hL, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : cb7 * (8 * Fm.CGam * y ^ 8) ≤ cb7 * ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left hk8 hcb.le
    push_cast
    nlinarith

end Fam

end Formalism.L2.SG.Pf.AllRowsCountBase
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarVolPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.DstarVolPf

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.Theta
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def frOf : Formalism.IndefR.Eqv.UI.Frames D (VS D) where
  ε := fun _ => Formalism.L2.SG.InstExistsPf.epsV D
  P := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose
  unit := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.1
  spec := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.2
  Λ := Formalism.L2.SG.InstExistsPf.Lv D
  Λ_fg := Formalism.L2.SG.InstExistsPf.L_fg D
  Λ_span := Formalism.L2.SG.InstExistsPf.L_span D
  Λ_dual := Formalism.L2.SG.InstExistsPf.L_dual D

theorem instOf_eq : Formalism.L2.SG.InstExistsPf.instOf D = Formalism.IndefR.Eqv.UI.instV (frOf D) := rfl

theorem lv_eq : (frOf D).Λ = Formalism.IndefR.Eqv.UI.Lv D (VS D) := rfl

abbrev IV : Formalism.MainNotions.S.AutInst := Formalism.IndefR.Eqv.UI.instV (frOf D)

def cdProdI : ENNReal := ∏ v : InfinitePlace D.host.F, (D.s.cdScale (VS D).rank ((frOf D).ε v) : ENNReal)

def muVI (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [SigmaFinite μf] : Measure (GA D (VS D)) :=
  cdProdI D • ((Formalism.IndefR.Eqv.UI.instV (frOf D)).muA μf).map (Formalism.IndefR.Eqv.UI.brg (frOf D))

def VolMeasOf : Prop :=
  ∀ (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    μf (Formalism.IndefR.Eqv.UI.instV (frOf D)).Kset = 1 →
    IsVolMeas D (VS D) (D.R.k + D.R.rS) (D.R.rS + 1) (muVI D μf)

theorem volMeasOf_of (hcd : cdScaleTie D) : VolMeasOf D := by
  intro μf _ _ hK
  have h1 : ∀ (v : InfinitePlace D.host.F) (i : Fin (D.R.k + D.R.rS)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i)) = true := fun v i => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 : ∀ (v : InfinitePlace D.host.F) (j : Fin (D.R.rS + 1)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j)) = false := fun v j => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  exact Formalism.L2.S.S7.ZsCovMeas.isVolMeas_muV (frOf D) hcd (lv_eq D) (fun _ => (Formalism.L2.SG.InstExistsPf.eSgn D).symm)
    h1 h2 (fun v => (D.s.cdScale_pos _ _).ne') μf hK

theorem cdScale_cast {n m : ℕ} (h : n = m) (ε : Fin n → Bool) :
    D.s.cdScale n ε = D.s.cdScale m (fun i => ε (Fin.cast h.symm i)) := by
  subst h; rfl

theorem cdScale_epsV :
    D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) = D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) := by
  rw [cdScale_cast D ((Formalism.L2.SG.InstExistsPf.rank_eq D).trans (dimS_eq D.R).symm)]
  rfl

section Gen

variable {I : Formalism.MainNotions.S.AutInst} (hb : AdBridgeIso I)

theorem mem_rr_iff' (x : I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF I ↔ toHA I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds I (toHA I hb) (toHA_isBridge I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J,
      h ∈ ratHA I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA I hb).injective hyx]

theorem isFD_image (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ν : Measure (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J))
    (hν : ν ≪ (I.muA μf).map (toHA I hb)) :
    IsFundamentalDomain (HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) (toHA I hb '' fund) ν := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : (I.muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' I μf
  haveI : (I.muA μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund (I.muA μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
  let e := (toHA I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF I :=
    { toFun := fun g => ⟨(toHA I hb).symm (g : HA _ _ _), (mem_rr_iff' hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA I hb x, (mem_rr_iff' hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((I.muA μf).map e) (I.muA μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' fund) ((I.muA μf).map e) := by
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : I.GA) * x) = (g : HA _ _ _) * e x
    show toHA I hb ((toHA I hb).symm g * x) = (g : HA _ _ _) * toHA I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  exact hfd.mono hν

end Gen

theorem covol_gen (hVM : VolMeasOf D) (hVol : VolTie D) (I : Formalism.MainNotions.S.AutInst)
    (hI : I = Formalism.IndefR.Eqv.UI.instV (frOf D)) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hf : I.IsFundDom (I.muA μf) fund) :
    I.vol μf fund / (μf I.Kset).toReal *
      ∏ _v : InfinitePlace I.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = volY0 D := by
  subst hI
  have hKc : IsCompact (IV D).Kset := Formalism.L2.SG.Closed.AutKCompact_holds (IV D)
  have hKo : IsOpen (IV D).Kset := by
    have h := (IV D).topf_open 1 le_rfl
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨hx, fun y hy => ⟨_, Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv _ hx hy, by simp⟩⟩
    · intro hx
      exact hx.1
  have hpos : 0 < μf (IV D).Kset := hKo.measure_pos μf ⟨1, Formalism.L2.SG.Pf.unitaryCongruence.K_one _⟩
  have hfin : μf (IV D).Kset < ⊤ := hKc.measure_lt_top
  set c := μf (IV D).Kset with hc
  let μ' : Measure (IV D).Gf := c⁻¹ • μf
  haveI : μ'.IsHaarMeasure := Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos.ne')
  have hfs : ∀ n, μ' (spanningSets μf n) < ⊤ := fun n => by
    show (c⁻¹ • μf) _ < ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hpos) (measure_spanningSets_lt_top μf n)
  haveI : SigmaFinite μ' :=
    ⟨⟨{ set := spanningSets μf, set_mem := fun _ => Set.mem_univ _, finite := hfs, spanning := iUnion_spanningSets μf }⟩⟩
  have hK1 : μ' (IV D).Kset = 1 := by
    show (c⁻¹ • μf) (IV D).Kset = 1
    rw [Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel hpos.ne' hfin.ne]
  have hV := hVM μ' hK1
  have hsig : (VS D).SigOK := D.sp.Y_sig 0
  have hsv : ∀ τ, (VS D).sig τ = (D.R.k + D.R.rS, D.R.rS + 1) := fun τ => D.sp.baseSpace_signature_eq τ
  obtain ⟨-, hall⟩ := hVol (VS D) _ _ hsig hsv
  obtain ⟨-, hfd⟩ := hall _ hV
  let hb : AdBridgeIso (IV D) := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (IV D)).1
  have hbrg : Formalism.IndefR.Eqv.UI.brg (frOf D) = toHA (IV D) hb := rfl
  have hμA : (IV D).muA μ' = c⁻¹ • (IV D).muA μf := by
    show (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod (c⁻¹ • μf) = c⁻¹ • (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod μf
    exact Measure.prod_smul_right _
  have hν : muVI D μ' ≪ ((IV D).muA μf).map (toHA (IV D) hb) := by
    unfold muVI
    rw [hbrg, hμA, Measure.map_smul]
    exact (Measure.smul_absolutelyContinuous).trans Measure.smul_absolutelyContinuous
  have hFD := isFD_image hb μf fund hf (muVI D μ') hν
  have key : muVI D μ' (toHA (IV D) hb '' fund) = ENNReal.ofReal (D.vol (VS D)) := hfd _ hFD
  haveI : BorelSpace (HAd (IV D)) := ⟨rfl⟩
  let e := (toHA (IV D) hb).toHomeomorph.toMeasurableEquiv
  have hmeas : Measurable (toHA (IV D) hb) := (toHA (IV D) hb).continuous.measurable
  have hS : MeasurableSet (toHA (IV D) hb '' fund) := (e.measurableSet_image).2 hf.1
  have hmap : muVI D μ' (toHA (IV D) hb '' fund) = cdProdI D * (c⁻¹ * (IV D).muA μf fund) := by
    unfold muVI
    rw [Measure.smul_apply, smul_eq_mul, hbrg, hμA]
    congr 1
    erw [Measure.map_apply hmeas hS]
    rw [Set.preimage_image_eq _ (toHA (IV D) hb).injective, Measure.smul_apply, smul_eq_mul]
  have hA0 : (IV D).muA μf fund ≠ 0 := by
    haveI : ((IV D).muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' (IV D) μf
    have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF (IV D)) fund ((IV D).muA μf) :=
      Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
    exact hfd0.measure_ne_zero (NeZero.ne _)
  have hcd0 : cdProdI D ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by simpa using (D.s.cdScale_pos _ _).ne'
  have hci0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin.ne
  replace key := hmap.symm.trans key
  have hAT : (IV D).muA μf fund ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.mul_top hci0, ENNReal.mul_top hcd0] at key
    exact ENNReal.ofReal_ne_top key.symm
  have hL0 : cdProdI D * (c⁻¹ * (IV D).muA μf fund) ≠ 0 := mul_ne_zero hcd0 (mul_ne_zero hci0 hA0)
  have hvpos : 0 < D.vol (VS D) := by
    by_contra hle
    push_neg at hle
    rw [ENNReal.ofReal_of_nonpos hle] at key
    exact hL0 key
  have hR := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_ofReal hvpos.le, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv] at hR
  have hcdR : (cdProdI D).toReal = ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) := by
    unfold cdProdI
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    show ((D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) : ENNReal)).toReal = _
    rw [cdScale_epsV]
    rfl
  rw [hcdR] at hR
  show ((IV D).muA μf fund).toReal / c.toReal *
      ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = D.vol (VS D)
  rw [← hR]
  ring

section Record

variable {D}

theorem dstarVolV_of (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVolV X :=
  covol_gen D (volMeasOf_of D hcd) hVol X.B.I (h.trans (instOf_eq D)) X.B.μf X.B.fund X.B.fund_spec

theorem dstarVol_holds (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) (hT : dsigTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVol X :=
  Formalism.L2.SG.Pf.RowDictPf.dstarVol_of X hT (dstarVolV_of X h hVol hcd)

end Record

end Formalism.L2.SG.Pf.DstarVolPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoPhi
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.Theta Formalism.L2.SG.RowDict
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTOntoPhi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem regAlg : (∀ a b, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ X.B.R 1 = 1 ∧ ∀ a F, ‖X.B.R a F‖ = ‖F‖ := by
  have := X.B.sf
  have := X.B.haar
  exact Formalism.L2.SG.Pf.reg_alg Formalism.L2.SG.Closed.UnimodGf_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec

theorem inner_reg (a : X.B.I.GA) (x z : L2X X) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨hmul, hone, hiso⟩ := regAlg X
  have := Formalism.L2.SG.Pf.inner_orbit X.B.R hmul hiso a⁻¹ 1 x z
  rw [hone, ContinuousLinearMap.one_apply, inv_inv, mul_one] at this
  exact this.symm

variable {X}

end Formalism.L2.SG.EvalTOntoPhi

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
section
namespace Formalism.L2.SG.Pf

theorem fibFinAll_holds : Formalism.L2.SG.TermTieOf.FibFinAll := FinXP.fibFin_holds

theorem pairIndepAll_holds : Formalism.L2.SG.TermTieOf.PairIndepAll :=
  FinXP.pairIndep_of Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds

theorem iotaRowC_holds : FinXP.IotaRowC := fun _ _ Y _ _ s₁ s₂ hr =>
  Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (congrArg (fun q => q.1.1) hr) (congrArg (fun q => q.2.1.1) hr)
    (congrArg (fun q => q.2.2) hr)

theorem pairTiesAll_holds : Formalism.L2.SG.TermTieOf.PairTiesAll := FinXP.pairTies_of iotaRowC_holds

theorem atPtRelevantAll_holds : FinXP.AtPtRelevantAll := FinXP.atPtRelevant_holds

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem finXC_of (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  FinXP.finX_holds hWu hRF Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.UMatMulInv
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem map_span_G (g : Formalism.REAL.UJ (X.B.I.ε v)) (Fp : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ)
    (S : Set (Fin (D.R.rS + 1))) (y : Fin X.B.I.n → ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S)) :
    uMat g⁻¹ *ᵥ y ∈ Submodule.span ℂ (Fp '' S) := by
  have e : Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S) =
      (Submodule.span ℂ (Fp '' S)).map (Matrix.mulVecLin (uMat g)) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [e] at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  have h1 : uMat g⁻¹ * uMat g = 1 := by simp [uMat]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact hz

section Main

variable (hw : OkPt X u u' w)

def yU (c : FreeE w → ℂ) (hw : OkPt X u u' w) : Formalism.REAL.UJ (X.B.I.ε v) :=
  mkUJ _ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) (yM_unit X u u' w v hw c)

theorem T_sub (c : FreeE w → ℂ) (x : Fin X.B.I.n → ℂ) :
    (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ x =
      uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ
        (uMat (gamW X u u' w v) *ᵥ x) - uMat (gamW X u u' w v) *ᵥ x) := by
  have hc : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) =
      uMat (gamW X u u' w v)⁻¹ * uMat (yU X u u' w v c hw) * uMat (gamW X u u' w v) := rfl
  have hy : uMat (yU X u u' w v c hw) = Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := rfl
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  rw [hc, hy, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem G_eq (b : Fin (D.R.rS + 1)) : Gw X u u' w v b = uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b := rfl

include hw in
theorem TG_comb (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b -
      Gw X u u' w v b) = ∑ b', (Cw w c - 1) b' b • frm X u' D.host.rdE v b' := by
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  have hA : ∀ x, uMat (gamW X u u' w v)⁻¹ *ᵥ (uMat (gamW X u u' w v) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [yM_G X u u' w v hw c b]
  simp only [G_eq, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

include hw in
theorem inN_u' (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))
      (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v)) := by
  have hC := isUB_Cw w c
  refine ⟨⟨fun a => ?_, ?_⟩, fun x hx => ?_⟩
  · show (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    rw [T_sub, e_eq X u' v a, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, Matrix.mulVec_smul,
      ← G_eq, TG_comb X u u' w v hw c]
    exact Submodule.smul_mem _ _ (span_frm_le X u' v a.1 a.2.le (comb_mem X u' v hC a.castSucc))
  · rw [T_sub, ← frm_last X u' v, ← G_eq, TG_comb X u u' w v hw c]
    exact span_frm_le X u' v D.R.rS le_rfl (comb_mem X u' v hC (Fin.last D.R.rS))
  · rw [T_sub]
    have hperp := Yc_perpG _ _ _ (Tw u) (Tw u') (piW w) (blkW w) (gram_frm X v u _) (hGG_w X u u' w v) (piW_invol w)
      (piW_blk w) (piW_anti w) (hZ_w X u u' w hw v) (hgap_w X u u' w v hw) hC (uMat (gamW X u u' w v) *ᵥ x)
      (fun b hb => by
        obtain ⟨b0, rfl⟩ : ∃ b0 : Fin D.R.rS, b = b0.castSucc := ⟨⟨b.1, Fin.val_lt_last hb⟩, Fin.ext rfl⟩
        rw [G_eq, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (gamW X u u' w v), Matrix.mulVec_mulVec,
          Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec, frm_castSucc, hJs_l, hx b0, mul_zero])
    have h2 := map_span_G X v (gamW X u u' w v) (frm X u' D.host.rdE v) _ _ hperp
    rw [lt_last_set] at h2
    exact span_frm_le X u' v D.R.rS le_rfl h2

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end


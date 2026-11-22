import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiExThetaGeneral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Outright
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0354

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSiteStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  first | exact @GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN | exact GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN | (intros; apply GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem bAt_orth_lev : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj a
  cases j with
  | zero =>
    refine ⟨?_, fun a' => rfl⟩
    exact J.Gd.cmp.B_std.1
  | succ j =>
    refine ⟨(H.core j hj _).std, fun a' => J.oneB j hj _ _⟩

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLawAndFixedCoordinateStabiliserLaw
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem site_law_xiIn : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pair → S.Pos → S.Move → S.Away → S.Law ∧
    Lt.LawInLt (sysS H X std) S.hfin S.E S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT ∧
    AdmLoc.XiIn (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPair hPos hMove hAway
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.TieBase.base_data t
  obtain ⟨hcl, hSS⟩ := GlobalTheory.BadPrimes.lev_pos_and_noConj J.A J.dtU J.a J.pins J.tie
  have hmm : (sysS H X std).mm = D.R.m := (DelB.sysS_ranks S).1
  have hLaw : S.Law :=
    GlobalTheory.TwU.LawAll.kapLawLt_frecG D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
      (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
      (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair hPos hMove
  refine ⟨hLaw, ?_, ?_⟩
  · intro j hj c L0 La' ε hrep hL' hε
    letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    exact GlobalTheory.TwU.KapLawLt.stab (h := hLaw) (hj := hj) c L0 La' ε (repOf_lat _ S.hfin j (c, L0) hrep) hL' hε
  · intro v j hj
    have hRB := GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt (D.what₂.places.resChar w) (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau
      (hT.gat_pos u w hg)
      (Formalism.L2.PairingIndexBounds.F.FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT)) hLaw
    exact hRB.2 v j hj
      (GlobalTheory.XiGen.xiEx_theta_general D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq
        (Formalism.L2.PairingIndexBounds.Rec.model_at_split_places_holds D) (Formalism.L2.PairingIndexBounds.Rec.split_place_moves_compose D) (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
        (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair v j hj (hAway v j (hmm ▸ hj)))

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeights
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem liftWt_of_lt (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) (r : ℕ) (hr : r < m + j * (t + 1) + 1) (h : r < m + 1) :
    liftWt t m lam w j ⟨r, hr⟩ = lam ⟨r, h⟩ := by
  simp [liftWt, h]

theorem liftWt_blk (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j b : ℕ) (hr : m + 1 + b * (t + 1) < m + j * (t + 1) + 1) :
    liftWt t m lam w j ⟨m + 1 + b * (t + 1), hr⟩ = -w (b + 1) := by
  have hd : b * (t + 1) / (t + 1) = b := Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [liftWt]
  rw [dif_neg (show ¬ (m + 1 + b * (t + 1) < m + 1) by omega)]
  simp only [Nat.add_sub_cancel_left, hd]

set_option maxHeartbeats 1000000 in

theorem wtOK_sites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → WtOK (sysS H X std) D (hT.gat_pos u w hg) u μ j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj ⟨a⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hw0 := ((H.core j hj1) (((I.at' j hj1).st.eC.symm a).1)).wt
  have hrk := ((I.at' j hj1).st.loc (((I.at' j hj1).st.eC.symm a).1)).rk
  unfold WtTie at hw0
  rw [J.pos j hj1] at hw0
  have ht : (sysS H X std).t = D.R.t := X.fl_t
  have hk : (sysS H X std).G.P.m + 1 = D.R.k := by
    have := (lev0At J.Gd u w hg).A.rk
    simpa [Ranks.N] using this
  set pos := hT.gat_pos u w hg with hpos
  have hA : ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)) (r : ℕ) (hr : r < (sysS H X std).G.P.m + 1),
      (((sysS H X std).G.P.lam0 v s ⟨r, hr⟩ : ℤ) : ℚ) = hcToWeightQ (D.hcW u (pos ⟨v, s⟩)).u ⟨r, by omega⟩ := by
    intro v s r hr
    have hr' : r < (sysS H X std).G.P.m + (j + 1) * ((sysS H X std).t + 1) + 1 := by omega
    have h1 := hw0 v s ⟨r, hr'⟩
    have h3 : (gatJ Lv (j + 1)).P.lam0 v s ⟨r, hr'⟩ = (sysS H X std).G.P.lam0 v s ⟨r, hr⟩ :=
      liftWt_of_lt (sysS H X std).t (sysS H X std).G.P.m ((sysS H X std).G.P.lam0 v s) (fun i => (sysS H X std).w v i s) (j + 1) r hr' hr
    rw [h3] at h1
    rw [h1]
    have h2 := (I.at' j hj1).M.lam_eq (j + 1) hj1 (pos ⟨v, s⟩) ((finCongr hrk) ⟨r, hr'⟩)
    rw [dif_pos (show ((finCongr hrk) ⟨r, hr'⟩ : ℕ) < D.R.k from (by simp; omega))] at h2
    exact h2
  have hB : ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)) (b : ℕ) (hb : b ≤ j),
      (((sysS H X std).w v (b + 1) s : ℤ) : ℚ) = wG D.R ((D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩) (b + 1) := by
    intro v s b hb
    have hlt : b * ((sysS H X std).t + 1) < (j + 1) * ((sysS H X std).t + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.succ_pos _)
    have hr' : (sysS H X std).G.P.m + 1 + b * ((sysS H X std).t + 1) < (sysS H X std).G.P.m + (j + 1) * ((sysS H X std).t + 1) + 1 := by
      omega
    have h1 := hw0 v s ⟨_, hr'⟩
    have h3 : (gatJ Lv (j + 1)).P.lam0 v s ⟨_, hr'⟩ = -((sysS H X std).w v (b + 1) s) :=
      liftWt_blk (sysS H X std).t (sysS H X std).G.P.m ((sysS H X std).G.P.lam0 v s) (fun i => (sysS H X std).w v i s) (j + 1) b hr'
    rw [h3] at h1
    have h2 := (I.at' j hj1).M.lam_eq (j + 1) hj1 (pos ⟨v, s⟩) ((finCongr hrk) ⟨_, hr'⟩)
    have hv : ((finCongr hrk) ⟨_, hr'⟩ : ℕ) = D.R.k + b * (D.R.t + 1) := by
      simp only [finCongr_apply, Fin.coe_cast]
      rw [← hk, ← ht]
    have hd : (D.R.k + b * (D.R.t + 1) - D.R.k) / (D.R.t + 1) = b := by
      rw [Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
    have he : ∀ (b' : ℕ) (hb' : b' < D.R.m), b' = b → (D.hcW u (pos ⟨v, s⟩)).e ⟨b', hb'⟩ = (D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩ := by
      rintro b' hb' rfl; rfl
    rw [dif_neg (show ¬ (((finCongr hrk) ⟨_, hr'⟩ : Fin _) : ℕ) < D.R.k by rw [hv]; omega)] at h2
    rw [he _ _ (by rw [hv, hd]), hv, hd] at h2
    have h4 : ((-((sysS H X std).w v (b + 1) s) : ℤ) : ℚ) = -wG D.R ((D.hcW u (pos ⟨v, s⟩)).e ⟨b, by omega⟩) (b + 1) := by
      rw [h1]; exact h2
    push_cast at h4
    linarith
  have hcT : ∀ i, ((CmpJ.cTw D i : ℤ) : ℚ) = (i : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
    intro i
    obtain ⟨c, hc⟩ := D.R.t_odd
    have h2 : i * (D.R.t + 1) / 2 = i * (c + 1) := by
      rw [hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, ← mul_assoc, mul_comm i 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    simp only [CmpJ.cTw, h2]
    push_cast
    rw [hc]
    push_cast
    ring
  refine ⟨(GlobalTheory.TwV.DelB.sysS_ranks S).2.2.2 j, ?_, ?_, ?_⟩
  · intro τ i
    generalize hvs : pos.symm τ = vs
    obtain ⟨v, s⟩ := vs
    have hτ : τ = pos ⟨v, s⟩ := by rw [← hvs]; simp
    subst hτ
    have hS := Formalism.L2.KerInert.SecondKernelSharpWeights.sharp_weight_formula D ex.tw u μ j hj (pos ⟨v, s⟩) i
    have hL := (ex.tw.fm u μ).lam_eq j hj.le (pos ⟨v, s⟩) i
    have hSs := (D.chTw u μ).sSharp_eq j hj (pos ⟨v, s⟩)
    have hwj := hB v s j le_rfl
    have hk' : (D.gat u w hg).P.m + 1 = D.R.k := hk
    have hcomm := Nat.mul_comm j (D.R.t + 1)
    have hiN : i.1 < D.R.k + j * (D.R.t + 1) := by have := i.2; simp only [Ranks.N] at this; exact this
    apply Int.cast_injective (α := ℚ)
    simp only [hvs, Sys.nuv, nu]
    by_cases hr : i.1 < D.R.k
    · rw [if_pos (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1 by omega)]
      simp only [lamI]
      rw [dif_pos (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1 by omega)]
      have hl0 := hA v s i.1 (by omega)
      rw [dif_pos hr] at hL
      simp only [Nat.add_sub_cancel]
      push_cast
      simp only [Formalism.BasicNotions.wG, sExp', Ranks.N] at hwj hSs
      push_cast at hS hSs hwj
      rw [hl0]
      linarith
    · have hjt : (j + 1) * (D.R.t + 1) = j * (D.R.t + 1) + (D.R.t + 1) := by ring
      rw [if_neg (show ¬ (1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ (sysS H X std).G.P.m + 1) by omega)]
      rw [if_pos (show (sysS H X std).G.P.m + 1 < i.1 + 1 ∧ i.1 + 1 ≤ NN (sysS H X std).G.P.m (sysS H X std).t (j + 1) by
        simp only [NN]; rw [ht]; omega)]
      have hidx : (i.1 + 1 - ((sysS H X std).G.P.m + 2)) / ((sysS H X std).t + 1) = (i.1 - D.R.k) / (D.R.t + 1) := by
        rw [ht]; congr 1; omega
      have hb : (i.1 - D.R.k) / (D.R.t + 1) < j := by
        apply Nat.div_lt_of_lt_mul; omega
      have hwb := hB v s ((i.1 - D.R.k) / (D.R.t + 1)) hb.le
      rw [dif_neg hr] at hL
      rw [hidx]
      push_cast
      simp only [Formalism.BasicNotions.wG, sExp', Ranks.N] at hwj hSs hwb hL
      push_cast at hS hSs hwj hwb hL
      linarith
  · intro τ
    have hwj := hB (pos.symm τ).1 (pos.symm τ).2 j le_rfl
    have hp : pos ⟨(pos.symm τ).1, (pos.symm τ).2⟩ = τ := by simp
    rw [hp] at hwj
    simp only [wT]
    have hSs := (D.chTw u μ).sSharp_eq j hj τ
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hwj, hSs, hcT]
    simp only [Formalism.BasicNotions.wG, sExp', Ranks.N]
    push_cast
    ring
  · intro τ
    have hwj := hB (pos.symm τ).1 (pos.symm τ).2 j le_rfl
    have hp : pos ⟨(pos.symm τ).1, (pos.symm τ).2⟩ = τ := by simp
    rw [hp] at hwj
    simp only [wT]
    have hSd := (D.chTw u μ).sDiv_eq j hj τ
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hwj, hSd, hcT]
    simp only [Formalism.BasicNotions.wG, sExp, Ranks.N]
    push_cast
    ring

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStep
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.MvS

theorem cast_lev {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) (κ : (S.K β).lev.U) :
    ∃ κ' : (St.K (St.chOf c')).lev.U, κ'.1 = κ.1 ∧ (St.K (St.chOf c')).lev.chi κ' = (S.K β).lev.chi κ := by
  subst hSt hc' h hβ
  exact ⟨κ, rfl, rfl⟩

set_option maxHeartbeats 2000000 in

theorem pt_step {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (β : S.Ch) (hC : S.Core e β) (a : S.cmpt β)
    (γ : ((S.charts.gat β).lev a).Γ) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hg' : ∀ v, ((S.charts.gat β).lev a).smul γ L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : (S.loc β).IsPt a g x.1) (hx' : (S.loc β).IsPt a g' x'.1) :
    ∃ κ : (S.K β).lev.U, x'.1 = GlobalTheory.TwU.ratA D.host.F ((S.loc β).gamI a γ) * x.1 * κ.1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((S.K β).lev.chi κ : ℂˣ) : ℂ) ∧
        algebraMap G.O G.Kf ((((S.charts.gat β).lev a).χ γ : G.Oˣ) : G.O) = e r := by
  obtain ⟨κa, hκa⟩ := awayEx_of hC.good (S.K β).lev hC.gam a γ
  obtain ⟨ra, hra1, hra2⟩ := hC.chi a γ κa hκa
  obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.TwV.Xc.isPt_move_eq _ _ _ _ _ _ (S.loc β) _ _ _ _ (S.K β).lev hC.good hC.int hC.hypP hC.actB hC.bad_p a γ
    (hC.gamU a γ) κa hκa g g' (fun v => (hg' v).symm.trans (PStabEq.smul_colSpan (G := S.charts.gat β) a γ L g hg v)) x x' hx hx'
  refine ⟨κ, hκ1, ra⁻¹, ?_, ?_⟩
  · rw [map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc.MvS

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem moveBy_succ : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS i hi c La γ hL
  obtain ⟨⟨β, a⟩, rfl⟩ := (I.at' i hi).st.eC.surjective c
  have hC := H.core i hi β
  have hpt : ∀ L', ((I.at' i hi).st.loc β).IsPt a
      (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) L')
      (J.pt std (i + 1) hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).1 := by
    intro L'
    have h := (Joint.pt_succ_isPt t std J i hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).2
    have key : ∀ (b : Σ β : (I.at' i hi).st.Ch, (I.at' i hi).st.cmpt β), b = ⟨β, a⟩ → ∀ g x, ((I.at' i hi).st.loc b.1).IsPt b.2 g x →
        ((I.at' i hi).st.loc β).IsPt a g x := by
      rintro _ rfl g x h
      exact h
    exact key _ (Equiv.symm_apply_apply _ _) _ _ h
  have hb := Joint.basesAt_span t std J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) hL
  have hb' : ∀ v, (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) =
      colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La)) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
    intro v
    unfold basesAt
    exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj (i + 1)).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _))
      ⟨_, PStabEq.smul_colSpan (G := (I.at' i hi).st.charts.gat β) a γ La _ (fun v => hb v) v⟩
  obtain ⟨κ, hκ, r, hr1, hr2⟩ := MvS.pt_step (I.at' i hi).st _ β hC a γ La _ _ (fun v => hb v) (fun v => hb' v) _ _ (hpt La) (hpt _)
  have hc : (I.at' i hi).st.chOf (clsOf (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La) = β :=
    (clsOf_chart (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La hL).trans
      (congrArg Sigma.fst (Equiv.symm_apply_apply (I.at' i hi).st.eC ⟨β, a⟩))
  obtain ⟨κ', hκ'1, hκ'2⟩ := MvS.cast_lev (X.onCh i hi) (I.at' i hi).st (J.St (i + 1) hi) (J.st i hi) _
    (clsAt X H (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩) La) (clsAt_succ X H i hi _ La) β hc κ
  refine ⟨((I.at' i hi).st.loc β).gamI a γ, κ', hC.gamU a γ, ?_, ?_, r, ?_, hr2⟩
  · exact hκ.trans (congrArg _ hκ'1.symm)
  · intro hr v
    have hB : (J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc β).rk.symm) ((I.at' i hi).st.loc β).B := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).B = _
      rw [dif_pos hi]
      show Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).rk.symm)
        ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).B = _
      rw [Equiv.symm_apply_apply]
    have hJ : (J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        (gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc β).rk.symm) (finCongr ((I.at' i hi).st.loc β).rk.symm) := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).J = _
      rw [dif_pos hi]
    have hiw : (J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) = ((I.at' i hi).st.loc β).iw := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).iw = _
      rw [dif_pos hi]
      show ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).iw = _
      rw [Equiv.symm_apply_apply]
    have hρ : J.rho std v = ((I.at' i hi).st.loc β).iw v := (J.iw i hi β v).symm
    have hF : (J.fd std).frM (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v =
        (((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La))).toLinearMap)) *
          ((J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La)).1).map ((J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v)).submatrix
          (finCongr rfl) (finCongr rfl) := rfl
    rw [hF, hB, hJ, hiw, hρ]
    exact Mv0.frm_gen (Q := (sysS H X std).G.P.Qq v) _ ((I.at' i hi).st.loc β).rk hr (gramN D (i + 1) hi) ((I.at' i hi).st.loc β).B (((I.at' i hi).st.loc β).gamI a γ)
      (((I.at' i hi).st.loc β).iw v) _ (hC.actB a v γ)
  · exact hr1.trans (congrArg (fun z : ℂˣ => (z : ℂ)) hκ'2.symm)

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteNormalisingCharPowValuesInCoeffField
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.ChiPow

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem exists_upts_det {n : ℕ} (hn : 0 < n) (Gm : Matrix (Fin n) (Fin n) E) (C : GL (Fin n) E)
    (hC : cT (σ : E →+* E) C.1 * C.1 = Gm) (x : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ)
    (hx : (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * sigR σ _ x = 1) :
    ∃ Y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Y ∈ UPts σ Gm (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det Y = x := by
  set R := FiniteAdeleRing (𝓞 F) F
  let f : Fin n → (E ⊗[F] R)ˣ := Pi.mulSingle ⟨0, hn⟩ x
  have hf : f = Pi.mulSingle ⟨0, hn⟩ x := rfl
  let d : GL (Fin n) (E ⊗[F] R) := Units.map (Matrix.diagonalRingHom (Fin n) (E ⊗[F] R)).toMonoidHom
    (MulEquiv.piUnits.symm f)
  have hd : (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Matrix.diagonal (fun k => ((f k : (E ⊗[F] R)ˣ) : E ⊗[F] R)) := rfl
  let Cb := bc (inclE (F := F) R) C
  refine ⟨Cb⁻¹ * d * Cb, ?_, ?_⟩
  · have hsig : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE R) := by
      ext e
      simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    have hG : Gm.map (inclE (F := F) R) = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
      rw [← hC, Matrix.map_mul, ← Formalism.UG.P.cT_map (σ : E →+* E) (sigR σ R) (inclE R) hsig]
      rfl
    have hdd : cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [hd]
      unfold cT
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hn⟩
      · subst hk
        rw [hf, Pi.mulSingle_eq_same, mul_comm]
        exact hx
      · rw [hf, Pi.mulSingle_eq_of_ne hk, Units.val_one, map_one, one_mul]
    have h1 : cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
        cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    have h2 : (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 :=
      Units.mul_inv Cb
    show cT (sigR σ R) (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * Gm.map (inclE (F := F) R) *
      (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Gm.map (inclE (F := F) R)
    rw [hG, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
    calc _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          ((Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            simp only [Matrix.mul_assoc]
      _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            rw [h1, h2]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hdd, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, hd, Matrix.det_diagonal]
    rw [← Units.coe_prod, hf, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]
    calc _ = (Matrix.det ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          Matrix.det (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) * (x : E ⊗[F] R) := by ring
      _ = _ := by rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

end Gen

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc.ChiPow

set_option maxHeartbeats 4000000 in

theorem tw_ch_rat {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}
    (S : StepIn M i hi G) (β : S.Ch) (hr : S.ChRat β)
    (X : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.tw β).ch X : ℂ) := by
  obtain ⟨cl, hcl⟩ := (S.K β).y_bij.2 (Quotient.mk'' X)
  have hrel := Quotient.eq''.1 hcl
  rw [DoubleCoset.rel_iff] at hrel
  obtain ⟨h, hh, k, hk, hX⟩ := hrel
  obtain ⟨γ, hγ, hγh⟩ := hh
  have h1 := (S.tw β).ch_rat γ hγ h hγh.symm
  have h2 := (S.tw β).ch_U k hk
  obtain ⟨rc, hrc⟩ := hr cl
  refine ⟨(∏ τ, (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ (cTw D i))⁻¹ * rc, ?_⟩
  rw [hX, map_mul (S.tw β).ch, map_mul (S.tw β).ch, h2, mul_one, Units.val_mul, map_mul D.what₂.embLL, hrc, map_inv₀, map_prod]
  congr 1
  have e1 : ∏ τ, D.what₂.embLL (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det ^ cTw D i) =
      ∏ τ, (embT D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ cTw D i :=
    Finset.prod_congr rfl fun τ _ => by rw [map_zpow₀, tEL_emb]
  rw [e1]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem chiI_pow_rat : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c x hx
  cases j with
  | zero => exact ⟨1, by simp⟩
  | succ i =>
    have hi : i + 1 ≤ D.R.m := hj
    have hxc : (x : AfE D.host.F D.host.E) * sigR (sigD D) _ x = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨Y, hY, hYd⟩ := ChiPow.exists_upts_det (sigD D) Nat.one_pos (1 : Matrix (Fin 1) (Fin 1) D.host.E) 1
      (by rw [Units.val_one, cT_one, Matrix.one_mul]) x hxc
    have hex : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x := ⟨⟨Y, hY⟩, hYd⟩
    have hchi : chiI J x = ((D.chiD (J.dtU hex.choose) : ℂˣ) : ℂ) := by
      unfold chiI
      rw [dif_pos hex]
    obtain ⟨Z, hZ, hZd⟩ := ChiPow.exists_upts_det (sigD D) (D.R.N_pos (i + 1)) (gramN D (i + 1) hi) (J.A.crd (i + 1) hi)
      (J.pins.crd_orth (i + 1) hi) x hxc
    let β := ((I.at' i hi).st.eC.symm c).1
    have htw := J.tw i hi β ⟨Z, hZ⟩ hex.choose (hex.choose_spec.trans hZd.symm)
    obtain ⟨r, hr⟩ := ChiPow.tw_ch_rat (I.at' i hi).st β (H.core i hi β).chRat ⟨Z, hZ⟩
    have ht : (sysS H X std).t = D.R.t := (GlobalTheory.TwV.DelB.sysS_ranks S).2.1
    refine ⟨r, ?_⟩
    rw [hr, htw, hchi, ht, Units.val_zpow_eq_zpow_val]
    rfl

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_chart_eq_of_same_component : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.chart_eq_of_comp | exact GlobalTheory.TwV.Xc.chart_eq_of_comp | (intros; apply GlobalTheory.TwV.Xc.chart_eq_of_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponentStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), (J.fd std).frM j (c, La) = (J.fd std).frM j (c, Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.frM_fd_comp | exact GlobalTheory.TwV.Xc.frM_fd_comp | (intros; apply GlobalTheory.TwV.Xc.frM_fd_comp <;> assumption)
end


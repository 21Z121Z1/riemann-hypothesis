import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0596
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdBNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0531
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembersStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_ranks_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  first | exact @GlobalTheory.MemberRanks.admissible_ranks_at_member | exact GlobalTheory.MemberRanks.admissible_ranks_at_member | (intros; apply GlobalTheory.MemberRanks.admissible_ranks_at_member <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoublingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  first | exact @GlobalTheory.ChainTw.Peel.qPeel_holds | exact GlobalTheory.ChainTw.Peel.qPeel_holds | (intros; apply GlobalTheory.ChainTw.Peel.qPeel_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberData

open Formalism.MainNotions.S in

theorem dataNW_of_val {C : Formalism.MainNotions.Inhab.FC} {cD ch : ℝ} (hC : Std C) {D : D7} (L : SizeData₂ D)
    (hV : Val C cD ch L) (hS : SizesAt L) (hR : ∀ u, GlobalTheory.Core.Rk.RankMu D u) : GlobalTheory.Core.Deg.DataNW D := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hk0 : 0 < D.R.k := by omega
  have hSc := Sc_eq' L
  have e1 : ∀ u τ, uOne D u τ 1 = (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := fun u τ => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 hk0, D.hcW_first u τ hk0]
  have e2 : ∀ τ, vOne D τ 1 = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := fun τ => vOne_succ τ 0 (by omega)
  have hCc : L.Cc = 2 := hV.Cc_eq.trans hC.2.1
  have hdu : ∀ u, 0 < D.duS u := fun u => by
    have h := hR u
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
    have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := sub_pos.2 (one_lt_pow₀ hT (by omega))
    have h0 : (0 : ℝ) < D.duS u := by rw [h]; positivity
    exact_mod_cast h0
  refine ⟨data1 L, data2, ?_, ?_, ?_, ?_, data7, data8,
    fun u => ⟨GlobalTheory.CollCompare.splits_level D u, T_mod D u⟩, hdu,
    Formalism.L2.SG.ResidEvFree.splitsE_g D 0, Formalism.L2.SG.ResidEvFree.splitsE_g D 1,
    discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D),
    fun u => ne_of_mod (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le (T_mod D u)⟩
  · intro u τ
    rw [e1, e2, ← hSc]
    by_cases ht : Formalism.MainNotions.S.IsTop D τ
    · obtain ⟨t, ht⟩ := ht
      have h1 := (L.top_u τ t hk0 ht).1
      have h2 := (L.cloud_v τ ⟨0, by omega⟩).2
      have h3 := (L.aT_win t).1
      have h4 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_Sc_le hS
      have h5 := L.Sc_pos
      have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      rw [h1]
      linarith
    · have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).1
      push_cast at this
      exact this
  · intro u τ ht
    have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).2
    push_cast at this
    rw [hCc] at this
    rw [e1, e2]
    linarith
  · intro u τ ht
    have hv := hV.hc.1 τ ⟨D.R.k - 2, by omega⟩
    have hu := (hV.hc.2.1 τ hk0 (fun h => ht ((isTop_iff τ).2 h))).2
    have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
    have hv' := vOne_succ τ (D.R.k - 2) (by omega)
    rw [← e] at hv'
    rw [uOne_last u τ, hv', hv, hu]
    norm_num
  · intro τ ht
    obtain ⟨t, ht⟩ := ht
    have hm0 : 0 < D.R.m := by omega
    have eb : bOne D τ 1 = (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, bOne_succ τ 0 hm0]
    have et : bTop D τ = (L.bT t : ℝ) + ((D.R.k : ℝ) - 1) / 2 := by
      unfold bTop
      rw [uOne_last D.u₀ τ, (L.top_u τ t hk0 ht).2]
      ring
    have h1 := L.top_b τ t hm0 ht
    obtain ⟨b1, hb, htop, -, -⟩ := hV.hc.2.2.1
    have hb0 := (hb τ ⟨0, hm0⟩).1
    have hbt := htop τ t ht
    have hbR : (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
      rw [hb0, hbt]
      push_cast
      ring
    have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _
    have hb'0 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_b'_nonneg (L := L)
    have hx1 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_x_ge (L := L)
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx1
    have hbT := L.bT_ge t
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    rw [eb, et]
    constructor <;> linarith

theorem val_congr {C C' : Formalism.MainNotions.Inhab.FC} {cD cD' ch ch' : ℝ} {D : D7} {L : SizeData₂ D} (h1 : C = C') (h2 : cD = cD')
    (h3 : ch = ch') (h : Val C cD ch L) : Val C' cD' ch' L := by
  subst h1 h2 h3
  exact h

theorem val_sizes_at (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p)
    (fun κ _ O _ _ => Std κ.C ∧ Val κ.C κ.cD κ.ch O.L ∧ SizesAt O.L) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ h52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, h1⟩ := szRow_sizesAt eps he h52 C hC
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h2⟩ := h1 cD hcD
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x0, h3⟩ := h2 ch hch
  refine ⟨x0, fun K hK hx β _ c b _ => ?_⟩
  obtain ⟨e1, e2, e3, e4, -⟩ := hK
  have hv : Val C cD ch β.O.L := val_congr e1 e2 e3 (β.p.pt_val β.val)
  have hs : β.O.L.sc = K.s := β.sc
  refine ⟨hC, hv, h3 β.D β.O.L ?_ ?_ hv⟩
  · rw [hs]; exact e4
  · rw [hs]; exact hx

theorem dataNW_at : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := fun hL p =>
  ((val_sizes_at hL p).and (GlobalTheory.Fam.MemberCount.member_rankMu hL p)).imp fun _ _ β _ _ _ _ _ H =>
    dataNW_of_val H.1.1 β.O.L H.1.2.1 H.1.2.2 H.2

end GlobalTheory.Fam.MemberData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedLatticeOfAdelicMatrixEqRowPoint
section
noncomputable section

namespace GlobalTheory.TopVal.DecoPt

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hasRes_red {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) :
    HasRes P (algebraMap E _ a) (redP P a) := by
  obtain ⟨r, s, hs, h⟩ := id ha
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (redP P a)
  refine ⟨t, ht, ?_⟩
  have h1 := reduction_spec P hs h
  rw [← ht, ← map_mul, eq_comm, Ideal.Quotient.eq] at h1
  have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 h1
  have h3 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    le_antisymm (HeightOneSpectrum.valuation_le_one (K := E) P s)
      (not_lt.1 fun hl => hs ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).1 hl))
  have h4 : P.valuation E (algebraMap (𝓞 E) E s * (a - algebraMap (𝓞 E) E t)) < 1 := by
    rw [mul_sub, h, ← map_mul, ← map_sub]
    exact h2
  rw [map_mul, h3, one_mul] at h4
  rw [← map_sub, valued_algebraMap]
  exact h4

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}

theorem adAt_pull {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (x : Sp E n) (i : Fin n) :
    adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x i) = algebraMap E _ ((p.fr P).symm x i) := by
  have e : ratM P.1 (p.fr P) = locM P.1 g := Matrix.ext fun i j => (h.fr P i j).symm
  have h1 := ratM_mulVec (P := P.1) (p.fr P) ((p.fr P).symm x)
  rw [LinearEquiv.apply_symm_apply, e] at h1
  have h2 := congrFun (congrArg (fun v => locM P.1 g⁻¹ *ᵥ v) h1) i
  simp only [Matrix.mulVec_mulVec] at h2
  rw [← locM_mul, inv_mul_cancel, locM_one, Matrix.one_mulVec] at h2
  rw [h2]
  simp only [GlobalTheory.Mem.Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE, locM, Matrix.map_apply]

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST (uSG SG Q) ∅ :=
  ⟨(forgetFr p, fun _ => 1), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_noFr {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : IsPtOf hc g (noFr p) := by
  refine ⟨h.uni, h.lat, h.f, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  show HasRes _ _ ((forgetDeco p).be w x i)
  by_cases hw : w.1 ∈ SG
  · rw [forgetDeco_be_of_mem p w hw]
    exact h.be ⟨w.1, hw⟩ x hx i
  · have hs : (p.fr (rightOf w hw)).symm x ∈ stdAt E n w.1 := by
      refine (p.2 (rightOf w hw) _).1 ?_
      show p.fr (rightOf w hw) ((p.fr (rightOf w hw)).symm x) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact le_locP _ _ hx
    have e : frBe w.1 (p.fr (rightOf w hw)) x = redV w.1 ((p.fr (rightOf w hw)).symm x) := if_pos hs
    rw [forgetDeco_be_of_not p w hw, e, adAt_pull h (rightOf w hw) x i]
    exact hasRes_red (mem_stdAt.1 hs i)

theorem decoOf_eq_forgetFr [NeZero n] {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    decoOf ST (uSG SG Q) g = forgetFr p :=
  Subtype.ext ((rlc_decoOf_val hc n ST (uSG SG Q) h.uni).trans (near_of_isPtOf (isPtOf_noFr h) 0).deco)

end General

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_eq_toRow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X), I.Ok → ∀ (a : I.ι) (y : GlobalTheory.Mem.Col2.TC.GA B (B.R.N B.R.m - 1)) (p : GlobalTheory.Mem.Col2.XPt (B.primes X) B.R I.sel (I.tup a)), GlobalTheory.Mem.Col2.TC.PtOf y p → GlobalTheory.TopVal.latOf I a y = GlobalTheory.Mem.Col2.toRow I.sel (I.tup a) p := by
  intro B X I _ a y p h
  letI := GlobalTheory.Mem.Col2.starE B
  exact decoOf_eq_forgetFr (F := B.fields.F) (E := B.fields.E) h

end GlobalTheory.TopVal.DecoPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EulerFactorFromDoubling
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Top

variable {D : D7}

theorem fockVec_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A H : HSp D} {sA : RealMat A} {sH : RealMat H}
    {f : WO A H → ℂ} (hf : IsThetaFunO ψ A H f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) : IsFockVec ψ θ A H sA sH f := by
  refine ⟨hf, 1, fun l hl => ?_⟩
  match l, hl with
  | [p], _ => exact hv p.1 p.2

theorem sphFun_of_param {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem downNe_of_hypotheses : GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm →
    GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D := by
  intro hDM hRSW hSP D hER ψ θ A W t χA χW om cA a β Z m u par sW Φ hDef hSigW hW0 hrank hη hom hPl hm hForm hOcc hNo
  obtain ⟨H, B, o, hd, hSigH, hSigB, hHr, hHsig, sH, hsH⟩ := GlobalTheory.T.exists_sum_hyperbolicPlanes_orthogonal_wittDecomposition D W t hSigW
  obtain ⟨c, hHyp⟩ := hForm.str
  have ht : W.rank + 5 ≤ t := hHyp.2.1
  have hBr : B.rank = W.rank + 2 * t := by have := o.rank_add; omega
  have hstd : IsStdChar D ψ (-1) := hom.std
  have h1 : IsHeckeChar D (1 : (AE D)ˣ →* Circle) := ⟨continuous_const, fun _ => rfl⟩
  have hr1 : ResEta D (1 : (AE D)ˣ →* Circle) 0 := by
    have h := resEta_parity (m := 0) (resEta_mul hom.resS (resEta_inv hom.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h
  obtain ⟨omH, homH⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ A H χA 1 hstd hom.hecS h1 hom.resS
    (resEta_parity hr1 (by omega))
  obtain ⟨omB, homB⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ A B χA χW hstd hom.hecS hom.hecT hom.resS
    (resEta_parity hom.resT (by omega))
  obtain ⟨omhB, homhB⟩ :=
    GlobalTheory.Core.Rk.exists_doubled_weilDatum GlobalTheory.weilRepresentationUnitaryPair D ψ A B χA χW omB homB
  obtain ⟨omhW, homhW⟩ :=
    GlobalTheory.Core.Rk.exists_doubled_weilDatum GlobalTheory.weilRepresentationUnitaryPair D ψ A W χA χW om hom
  have hAH : A.rank ≤ H.rank := by omega
  obtain ⟨f, hf, hf0, hfvac, hfsph, hfκ, hfoff⟩ :=
    GlobalTheory.T.exists_vacuumVector_principalCongruenceSupport D ψ θ A H χA omH (fun _ => 1) sH hDef.inf hη homH hDef.one hsH hAH β Z hPl
  have hfb := GlobalTheory.T.definite_real_group_fixes_split_space_weil_vacuum D ψ θ A H t χA omH sH hDef.inf hη homH hDef.one hsH hSigH hHr hHsig f hf hfvac
  obtain ⟨sB, LB, hsB, hLB, hbF, hbS⟩ :=
    GlobalTheory.T.boxProducts_orthogonalSum_target_cartan_fock D ψ θ A B W H o (fun _ => 1) sW sH hstd hDef.inf hOcc.cart hsH
  have hFs : IsFockVec ψ θ A B (fun _ => 1) sB (o.boxT A Φ f) := hbF Φ f hOcc.fock (fockVec_of_vac hf hfvac)
  have hSs : IsSphOff ψ A B (frameLat A) LB (under Z) (o.boxT A Φ f) :=
    hbS (frameLat A) (under Z) Φ f hOcc.sph hfsph
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  have hPair : Pair ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 :=
    { setting := ⟨by omega, by omega, by omega, hDef.inf, hDef.sig, hDef.cart, hDef.one, hsB, hDef.cA_eq⟩
      maj := hDef.maj
      maj_eq := hDef.maj_eq
      weil := homB
      covol := hν }
  have hu := hForm.mem
  have hu' := (Submodule.mem_inf.1 hu).2
  have huc : Continuous u := hu'.1
  have hul : ∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g := hu'.2.1
  have hKill := GlobalTheory.T.doubling_integrals_vanish_of_all_lifts_vanish D ψ A W χA χW om omhW hDef.sig hDef.pos hom homhW m hm u huc hul hNo
  have hφθ := GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hstd _ _ hFs.1 hFs.1
  have hφK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair omhB homhB _ _ hFs hFs
  obtain ⟨hPole, E₁, hE₁, hE₁0⟩ := GlobalTheory.T.doubling_witt_tower_reduction hRSW D ψ θ A cA a hDef hPl.two B W t hd hSigB hSigW hW0
    (by omega) hrank χW omhB omhW homhB homhW ν 𝓕 hν m hm u huc hul hKill _ hφθ hφK
  obtain ⟨hZF, hEC, hAn, hReg, hint⟩ :=
    GlobalTheory.T.regularised_theta_pairing_identity hDM D ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair omhB homhB m hm _ hFs u hu
  obtain ⟨hcc, -⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hDef.sig hDef.pos m hm
  have hRD := (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D A hcc (fun g => conj (u g))
    ⟨fun γ hγ g => by simp only [hul γ hγ g], Complex.continuous_conj.comp huc⟩).1
  have hμ : IsHeckeChar D χW⁻¹ :=
    ⟨(hom.hecT.1.inv : Continuous fun x => (χW x)⁻¹), fun x => by rw [MonoidHom.inv_apply, hom.hecT.2 x, inv_one]⟩
  have hcoef := GlobalTheory.Eis.coeffAt_neg_one_zeta_of_eisCoeffAt D A χW⁻¹ hμ m hm _ hEC hAn hReg _ _ hRD hRD hZF
    (sZero A B) E₁ hPole hE₁
  rw [hE₁0] at hcoef
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.levelPlaces_integral_nonzero_constant D ψ θ A cA a hDef B W H o χA χW omB om omH homB hom homH β Z hPl m hm u hu
    hForm.fix sW Φ hOcc f hf hf0 hfκ hfb hfoff ν 𝓕 hν
  have hsph : SphFun A (frameLat A) (under Z) u := sphFun_of_param hForm.param
  have hUn : Unram ψ A B χW (frameLat A) LB (under Z) (o.boxT A Φ f) (o.boxT A Φ f) :=
    ⟨GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A, hLB, fun v _ h2 => hPl.two v h2, hForm.unr, hSs, hSs⟩
  have hEq : EqRight (GlobalTheory.Eis.zeta A χW⁻¹ m (flat A a (swSec A B omhB ν 𝓕 (delta A B (o.boxT A Φ f) (o.boxT A Φ f)))
      (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)))
      (fun s => GlobalTheory.LFun.LSD D (under Z) par χW (s + 1 / 2) /
        GlobalTheory.LFun.dSfun D.host.E (under Z : Set (FinPl D)) A.rank B.rank s * C) := by
    refine ⟨A.rank + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    have h2 : (A.rank : ℝ) / 2 < s.re := by
      have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
      linarith
    obtain ⟨hI, hz⟩ := hint s h2
    rw [hz, hER ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair (frameLat A) LB (under Z) _ _ hFs.1 hFs.1 hUn
      m hm u hu u hu par hForm.param hsph s hs' hI, hC s]
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero]
    rw [hBr, hrank]
    push_cast
    ring
  have hcoef' : CoeffAt (GlobalTheory.Eis.zeta A χW⁻¹ m (flat A a (swSec A B omhB ν 𝓕 (delta A B (o.boxT A Φ f) (o.boxT A Φ f)))
      (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g))) ((t : ℂ) / 2) (-1) 0 := by
    rw [← hs0]
    exact hcoef
  exact GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function hSP D (under Z) W.rank t c par χW hHyp A.rank B.rank _ C _ hC0 hEq hcoef' rfl

end GlobalTheory.Core.Rk.Exh.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitness
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal

namespace GlobalTheory.TopVal

def DatVal {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {G : Type} [Group G] [Fintype G]
    {Pl0 T : Type} {A : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [aK : Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) A Ks) (tup : T → I.ι) : Prop :=
  ∃ c : Val B →ₛₗ[B.embLL] R.cX.W,
    (∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
      GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = R.cX.ρ γ.1 (c v)) ∧
    ∀ (t : T) (φ : Frm I (tup t)) (x : A.fam.amb.FR t), IsRes φ x →
      ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') y, HasMat h y → IsUni B y →
        (R.HX t).e (R.jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h) = c (val φ (latOf I (tup t) y))

theorem matEq_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hm : HasMat h y) :
    GlobalTheory.Mem.R3.MatEq (R3.matIn D.sp.X' 1 ((finHom D.sp.X').rangeRestrict h)) y := by
  refine ⟨Formalism.L2.Forms.rankP D, fun i j i' j' hi hj => ?_⟩
  have e1 : finCongr (Formalism.L2.Forms.rankP D) i = i' := Fin.ext hi
  have e2 : finCongr (Formalism.L2.Forms.rankP D) j = j' := Fin.ext hj
  rw [← e1, ← e2, ← hm.2 i j]
  unfold R3.matIn
  rw [mul_one]
  rfl

set_option maxHeartbeats 1000000 in

theorem datVal_rows (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : Bl.RowsT K w Z Wt p0) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := t.r.z.alg) t.r.z.R.toRealDat t.r.Y.tup := by
  obtain ⟨c, h1, h2, -, -⟩ := hs.1
  have h3 := t.r.z.pins.char.base.models.jX
  have h4 := t.r.z.lev.beta.2
  refine ⟨c, fun γ γE g hr hm v => h1 γ γE g hr hm v, fun s => ?_⟩
  have h5 : w.I.tup (t.r.Y.tup s) = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have key : ∀ (a : w.I.ι), w.I.tup a = s.1 → ∀ (φ : Frm w.I a) (x : (R3.famT t).A.fam.amb.FR s), IsRes φ x →
      ∀ (h : GA (w.D Z) (w.D Z).sp.X') y, HasMat h y → IsUni B y →
        t.r.z.R.B.jR s x ((finHom (w.D Z).sp.X').rangeRestrict h) = c (val φ (latOf w.I a y)) := by
    intro a ha
    obtain ⟨s, hs'⟩ := s
    change w.I.tup a = s at ha
    subst ha
    rintro φ x ⟨ok, hx⟩ h y hm hu
    have hx' : ((by with_unfolding_all exact ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a)).res ok φ :)) : (R3.famT t).A.fam.amb.FR ⟨w.I.tup a, hs'⟩) = x := by
      apply eq_of_heq
      exact (by with_unfolding_all exact (hx :))
    have hM := matEq_of_hasMat hm
    have e := h2 B.sp.cm ⟨w.I.tup a, hs'⟩ ⟨⟨ok⟩, φ⟩ ((finHom (w.D Z).sp.X').rangeRestrict h) ⟨y, hu⟩ (by rw [h4]; exact hM)
    have e2 := decoPt_mk B.sp.cm (B.R.N B.R.m - 1) ∅ (rowSG (B.primes w.px) w.I.sel (w.I.tup a)) ⟨y, hu⟩
    rw [← hx']
    refine Eq.trans ((by with_unfolding_all exact (e :))) (congrArg (fun d => c (val φ d)) e2)
  intro φ x hx h y hm hu
  exact (congrFun (h3 s x) _).trans (key _ h5 φ x hx h y hm hu)

set_option maxHeartbeats 1000000 in

theorem datVal_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := a.x.alg) a.x.R.toRealDat a.x.Y.tup := by
  have h := datVal_rows K B f T w Z Wt ex.p0 t hs
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  rw [← hT'] at h
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨(by with_unfolding_all exact (c :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h2 :))

set_option maxHeartbeats 1000000 in

theorem pkVal_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → q.x.what₂.r.z.Std → ∃ cv, GlobalTheory.TopVal.ValEqv (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) cv ∧ GlobalTheory.TopVal.PkVal (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) cv := by
  intro hL p K q c b hw hs
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := datVal_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a hs
  have h1 : DatVal q.w.I q.w.l q.Z (aK := x.alg) x.R.toRealDat x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : Bl.RPk b.R b.S => DatVal q.w.I q.w.l q.Z (aK := k.B.alg) k.B.Q.Rl.toRealDat k.P.I.tup) (Bl.rpkB b) := by
    rw [y.eq]
    exact h1
  obtain ⟨cv, h3, h4⟩ := h2
  exact ⟨cv, h3, h4⟩

end GlobalTheory.TopVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembersStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.large_gap_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  first | exact @GlobalTheory.Core.Rk.GapAt.rowE_bigGap | exact GlobalTheory.Core.Rk.GapAt.rowE_bigGap | (intros; apply GlobalTheory.Core.Rk.GapAt.rowE_bigGap <;> assumption)
end


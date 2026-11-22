import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0539
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0503

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsFifthBound
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.BigTop.Fun
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem rankGapBound_alt : _root_.GlobalTheory.BigTop.Fun.RankGapBound' := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps heps1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨1, fun C hC => ?_⟩
  obtain ⟨-, heP, hcTO, -, -, -, -, -, hfix⟩ := hF.1
  have hW : PageWin Fm := hF.2.1
  obtain ⟨x2, hx21, hx2⟩ := mul_pow_le_exp_rpow heps (6 * (⌈|Fm.Ct|⌉₊ + 1)) 25
  refine ⟨max (max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps))) (max (max x2 20480) ((2 * C) ^ 2)),
    fun x hx hx0 i p _ d _ => ?_⟩
  have hxa : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx8 : (8 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hxb : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx0
  have hxc : 20480 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx0
  have hxC : (2 * C) ^ 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  have hx1 : 1 < x := by linarith
  have hx0' : (0 : ℝ) < x := by linarith
  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) hx8 heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨-, hk⟩⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2' : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have hH1 : leafHypothesesConst d.O := ⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩
  have hH7 : LatticeConstantBound d.O p.Z.b := by
    show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
    exact (Lc_le_of_cloud_le d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
      (fun τ j => cloud_mem_Icc_Sc (Fm.L x i) τ j)).trans (Sc_le_scale_b (Fm.params x hx i))
  have hb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [Fm.L_x x i hx, Fm.L_eps x i]
  have hT : (Fm.parT x hx i).TO ≤ (Fm.D x i).R.t := by
    have a1 := (Fm.parT x hx i).split
    have a2 := (Fm.parT x hx i).nP_eq
    have a3 := (Fm.parT x hx i).nW_lo.1
    have hf : 1 ≤ (Fm.D x i).R.f := by
      have : 0 < (Fm.D x i).R.ord := (Fm.D x i).R.ord_pos
      unfold Ranks.f Ranks.n; omega
    have hr : 1 ≤ (Fm.D x i).R.r := by
      have := (Fm.D x i).R.m_add_three_le_k
      unfold Ranks.r; omega
    have a4 : 1 ≤ (Fm.parT x hx i).nWn :=
      le_trans (Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)) a3
    have a5 : (Fm.parT x hx i).TO * 1 ≤ (Fm.parT x hx i).TO * (Fm.parT x hx i).nWn := Nat.mul_le_mul_left _ a4
    have a6 : 1 * (Fm.D x i).R.r ≤ 8 * (Fm.D x i).R.f * (Fm.D x i).R.r := Nat.mul_le_mul_right _ (by omega)
    omega
  have hto : x ^ 377 ≤ ((Fm.D x i).R.t : ℝ) := by
    have e1 : Fm.cTO = ((377 : ℕ) : ℝ) := by rw [hcTO, heP]; norm_num
    have e2 := (hfix x hx i).2.2.2.2.2.2.2
    have e3 : x ^ Fm.cTO ≤ ((Fm.parT x hx i).TO : ℝ) := by rw [e2]; exact Nat.le_ceil _
    rw [e1, Real.rpow_natCast] at e3
    exact e3.trans (by exact_mod_cast hT)
  have htc : ((Fm.D x i).R.t : ℝ) ≤ x ^ (⌈|Fm.Ct|⌉₊ + 1) := by
    have e1 := (Fm.L x i).t_win.2
    rw [Fm.Ct_eq x i, Fm.L_x x i hx] at e1
    refine e1.trans ?_
    have e2 : x ^ Fm.Ct ≤ x ^ (((⌈|Fm.Ct|⌉₊ + 1 : ℕ)) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
      push_cast
      linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
    rwa [Real.rpow_natCast] at e2
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hkt : (Fm.D x i).R.k + (Fm.D x i).R.m + 4 ≤ (Fm.D x i).R.t := by
    have := (Fm.D x i).R.rank_add_five_le
    have := (Fm.D x i).R.m_add_three_le_k
    omega
  have hB := hx2 x hxb
  obtain ⟨l1, l2⟩ := design_lines_of_ranks x eps (Real.exp (x ^ eps)) (⌈|Fm.Ct|⌉₊ + 1) (Fm.D x i).R.k (Fm.D x i).R.m
    (Fm.D x i).R.f (Fm.D x i).R.t hxc heps1 (Fm.D x i).R.two_le_m hmf (Fm.D x i).R.f_le_k hkt htc hto hk hB
  have hL : 2 * Real.log (2 * C) ≤ Real.log p.Z.b := by
    rw [hb, Real.log_exp]
    have e1 : x ≤ x ^ (6 * (⌈|Fm.Ct|⌉₊ + 1)) := le_self_pow₀ hx1.le (by omega)
    have e2 : x ≤ Real.exp (x ^ eps) := by
      have : 0 ≤ x ^ (6 * (⌈|Fm.Ct|⌉₊ + 1)) := by positivity
      linarith
    have e3 : Real.log x ≤ x ^ eps := by
      rw [Real.log_le_iff_le_exp hx0']; exact e2
    have e4 : 2 * Real.log (2 * C) = Real.log ((2 * C) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have e5 : Real.log ((2 * C) ^ 2) ≤ Real.log x := Real.log_le_log (by positivity) hxC
    linarith
  refine GlobalTheory.SizeLeafCheck.tree_leaf_parameter_arithmetic_of_bounds d.O C p.Z.b hC hH1 hH7 ?_ ?_ hL
  · rw [hb]
    exact l1
  · exact l2
end GlobalTheory.BigTop.Fun
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumDTLevelPrime
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem ratDatum_dT_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha hTr t J hJ eT heT j hj α γ
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  have hS := ha.shape
  have hP : (fun v => v ∈ a.v.tP) = (fun v => ∃ i, v = (a.o.p i).v) := funext fun x => propext (hS.pre.tP x)
  have hPl : GlobalTheory.FinPl.Places a.o.p a.o.I (fun v => ∃ i, v = (a.o.p i).v) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, fun _ => Iff.rfl, fun i => (hS.pre.char i).2⟩
  have hR : GlobalTheory.FinPl.Reps (_root_.GlobalTheory.Fam.pk_z W).ψ (a.o.β j) (a.o.β (j + 1)) (a.g.x j).L (a.g.x (j + 1)).L
      (fun i => GlobalTheory.LatPair.phiOne (a.o.Q j i) (a.o.Q (j + 1) i)) a.o.I (fun v => ∃ i, v = (a.o.p i).v) (a.v.dT j) := by
    rw [← hP]; exact ⟨(ha.vis.atT j).1, hS.rep j hj⟩
  exact GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime I hAll.tr.ok hAll.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is _ _ _ _ _ hTr.pinX a.k a.ι a.o.p a.o.β a.o.Q
    hTr.std a.o.I hPl j hj α γ (a.v.dT j) hR eT heT
end GlobalTheory.Fam
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsLow
section
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
structure QuadraticExtensionData.ReadsStd (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  orb : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
      SameOrb (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (box _ ((J.G i).ϖ ^ (J.E i).M))
        ((J.E i).cos (J.π i ((J.G i).s + 1) β))
        (Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r)))
  std : ∀ j, j < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι
structure QuadraticExtensionData.ReadsLow (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  std : ∀ j, j < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → j + 1 ≠ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  injCh : ∀ j, j + 1 ≠ B.R.m → Function.Injective (J.ι j)
  first : Function.Surjective (J.ι 0)
  onto : Function.Surjective (J.ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m), j + 1 + 1 ≠ B.R.m → ∀ γ, γ ∉ Set.range (J.ι (j + 1)) → ∀ α z, J.A.xi j hj α γ z = 0
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]
end Free
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
def SumPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1
def ReferenceCore : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C
def ReferenceTheta : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C
def ReferenceWeight : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C
end GlobalTheory.RefSum
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sets
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
end Sets
section Hyp
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Hyp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
namespace Fit
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} (h : Fit p w j hρ ν)
include h
end Fit
end Point
def TwistConditions (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
    (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j
section AtTw
variable {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
  (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop}
theorem TwistConditions.and (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (h' : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q') : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => Q Fm x hx i p w j ∧ Q' Fm x hx i p w j :=
  Closed.imp (Closed.and h h') fun _ _ _ H =>
    let ⟨x0, K⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and H.1 H.2
    ⟨x0, fun x hx h0 i p r m w hw j => ⟨(K x hx h0 i p r).1 m w hw j, (K x hx h0 i p r).2 m w hw j⟩⟩
theorem TwistConditions.imp (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j → Q' Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q' :=
  Closed.imp h fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m w hw j => f Fm x hx i p r m w hw j (K x hx h0 i p r m w hw j)⟩
theorem TwistConditions.of_forall (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p => f Fm x hx i p⟩⟩⟩
end AtTw
def CanonicalExists : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∃ rd : Can p w j, IsCan p rd ∧
  ∃ (n : ℕ) (β : Module.Basis (Fin n) (Fm.D x i).what₂.LL (Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL)),
    LinearIndependent (FractionRing ((Fm.ex x hx i).nch.Oe w)) fun a => rd (β a)
def CanonicalProjection₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => ∀ rd : Can p w j, IsCan p rd → ∀ y,
  rd ((((R2 p).FW j).eOp fun g => (idemOf p.P.A3.A.X).coeff g) y) = eExt (Fm.D x i).nexp _ _ _ _ (rd y)
def TwAdmAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ =>
  IntegralHeckeForms.TwOK ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
                     (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) ∧
    IntegralHeckeForms.ClsQ (D := Fm.D x i) ((Fm.ex x hx i).nch.Q w) ∧ (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w)
def LowerBoundAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ => ∀ P : Pl (Fm.D x i).host.E,
  (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 * (Fm.D x i).host.pde *
    (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 ((Fm.ex x hx i).nch.twI w)
def ConditionAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good), RealPin p.R p.cG ρ →
  ρ.LevelOf (Fm.D x i).nexp → RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
def RationalityHypothesis : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j =>
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' ((Fm.ex x hx i).nch.twI w) j hV' ∧
      (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ ((Fm.ex x hx i).nch.twI w) j b →
        RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j b
theorem twist_at_statement_of_ratHypAt (h : _root_.GlobalTheory.BigOn.Exp.RationalityHypothesis) (hR : RatStep) : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp h fun Fm x hx i _ _ _ _ _ j ⟨T', _, Rl', cG', S', YS', F', κ', v₀', O', hV', h1, h2, h3⟩ ρ hρ hp hL =>
    h3 ρ hρ _ (hR _ _ _ _ _ _ T' Rl' cG' S' YS' F' κ' v₀' O' ρ hρ _ j _ hV' (h2 ρ hp) hL
      ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩ h1)
def CompatibilityRational : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀,
  IsNorm p.R p.v₀ (Z.ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧ RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def RecursiveSide : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀, RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) →
  Submodule.span ((Fm.ex x hx i).nch.Oe w) ((fun a => (1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ (Fm.D x i).nexp.th _ _ _ a) ''
      IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) = baseLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧
  Submodule.span ((Fm.ex x hx i).nch.Oe w) (incl (Fm.D x i).nexp _ _ _ ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) ''
      ⋃ a ∈ IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) = twLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def AdaptedExistence₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w _ => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ →
  ∃ ρ' : Setup (Fm.D x i).ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ'
def ConjugateBase : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → baseLat p w j hρ ν = baseLat p w j hρ' ν'
def ConjugateTwist : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → twLat p w j hρ ν = twLat p w j hρ' ν'
def TwistCharacter : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → Adapted p w ρ →
  ChrEq (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
      (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi (p.Tp.psi w) ∧
    p.R.xi (p.R.mu ((Fm.D x i).plEq w)) = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi *
      (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi
def CanonicalFits (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (w : (Fm.D x i).what₂.places.Pl)
    (j : Fin (Fm.D x i).R.m) (ρ : Setup (Fm.D x i).ntw), ρ.Good → ℂ → Can p w j → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ) (rd : Can p w j), Fit p w j hρ ν → IsCan p rd →
    Q Fm x hx i p w j ρ hρ ν rd
def BaseUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realBase p rd ≤ baseLat p w j hρ ν
def BaseLowerBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => baseLat p w j hρ ν ≤ realBase p rd
def TwistUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realTw p rd ≤ twLat p w j hρ ν
def TwistLowerBound : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => twLat p w j hρ ν ≤ realTw p rd
def InductionConditions : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalExists ∧ _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwAdmAlt ∧ _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace ∧ _root_.GlobalTheory.BigOn.Exp.CompatibilityRational ∧ _root_.GlobalTheory.BigOn.Exp.RecursiveSide ∧ _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateBase ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateTwist ∧ _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistLowerBound
theorem exists_exportTie_fit_at_tw (h1 : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (h2 : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) (h3 : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂) : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => Nonempty (ExportTie p.nexp p.v₀) ∧
    ∀ Z : ExportTie p.nexp p.v₀, ∃ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), SameBut Z.ρ ρ ∧ Fit p w j hρ ν :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 h3)) fun _ _ _ _ _ _ hm _ _ _ ⟨a1, a2, a3⟩ => ⟨hm.2.2.series, fun Z =>
    let ⟨ρ, hρ, hs, ha⟩ := a3 Z.ρ Z.good Z.pin
    have hL := levelOf_of_sameBut hm.2.2 Z.good hρ Z.pin ha.1 hs (levelOf_exportTie Z)
    let ⟨ν, hn, hr⟩ := a2 ρ hρ ha.1 hL
    ⟨ρ, hρ, ν, hs, ha, hn, ⟨hr.1, hr.2.1 _ _ _ a1.1 a1.2.1⟩, hL⟩⟩
theorem InductionConditions.exportSt (h : _root_.GlobalTheory.BigOn.Exp.InductionConditions) : _root_.GlobalTheory.BigOn.ExportedStatement := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine Closed.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.exists_exportTie_fit_at_tw h3 h4 h7) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h5 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h6 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h8 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h9
    (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h10 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h11 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h12 h13)))))))))) fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m v hv j => ?_⟩
  obtain ⟨⟨⟨Z⟩, a0⟩, ⟨rd, hc, hβ⟩, a2, a5, a6, a8, a9, a10, a11, a12, a13⟩ :=
    K x hx h0 i p r m ((Fm.D x i).plEq.symm v) (by rwa [Equiv.apply_symm_apply]) j
  obtain ⟨ρ, hρ, ν, hs, hf⟩ := a0 Z
  obtain ⟨hN, hR⟩ := a5 Z
  obtain ⟨r1, r2⟩ := a6 Z hR
  have b1 := le_antisymm (a10 ρ hρ ν rd hf hc) (a11 ρ hρ ν rd hf hc)
  have b2 := le_antisymm (a12 ρ hρ ν rd hf hc) (a13 ρ hρ ν rd hf hc)
  simp only [realBase, realTw, Equiv.apply_symm_apply] at b1 b2
  exact ⟨rd, hβ, a2 rd hc, (b1.trans (a8 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r1.symm,
    (b2.trans (a9 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r2.symm⟩
end GlobalTheory.BigOn.Exp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
namespace GlobalTheory.ShareOn
section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
end Model
section Point
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p _ _ => ∀ i, ModelAt p i (Fm.parT x hx ι).TO
def SharedWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  ShareW p i (1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3))
def BadWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  BadW p i (Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))))
end GlobalTheory.ShareOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.L2.Host (CharFrame HChar TupTied)
open GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug
namespace GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace Side
variable {D : D7} {nch : NChoice D} (s : Side D nch)
end Side
section Wit
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
def sideOf_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n) : Side (w.st Z).toD7 nch :=
  { G := _, Pl0 := _, I0 := _, T := _, A3 := _, J := t.r.z.core, R := t.r.z.R, P0 := t.r.z.F.P0, ψ0 := t.r.z.F.ψ0, cG := t.r.z.cG,
    v₀ := t.r.z.geo.v₀, S := _, YS := c.row.nexp, cf := GlobalTheory.Mem.Col2.TC.cf w.I w.l Z, tp := n.tp }
end Wit
def ExponentialNormChoice (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ _ _ _ _ t _ n xd c =>
  PLift ((_root_.GlobalTheory.PlugPt.sideOf_alt t n c).Export xd) × PUnit.{2}
structure ExtensionReading (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) : Type 2 where
  rd : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (xd : ThData (w.D Z)),
    𝒮.Nx K B f T w Z Wt p0 t nch n xd → _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.PlugPt.ExponentialNormChoice hL) K B f T w Z Wt p0 t nch n xd
def HasExponent' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.PlugPt.ExponentialNormChoice hL K B f T w Z Wt p0 t nch n xd c)
def ExtensionReading.of {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (Rx : RPosition) {E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} (h : _root_.GlobalTheory.PlugPt.HasExponent' E) (Sx : SPosition) (Ox : OComponent₂) :
    _root_.GlobalTheory.PlugPt.ExtensionReading hL ⟨Rx, _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL E, Sx, Ox⟩ :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨y.1, Classical.choice (h _ _ _ _ _ _ _ _ _ _ _ _ _ y.2)⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {𝒮 : Slots}
def sideOfWeightedPoint (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) {K : Ctx} (p : WPt 𝒮 K) : Side (p.w.D p.Z) p.O.ex.nch :=
  _root_.GlobalTheory.PlugPt.sideOf_alt p.x.what₂ p.x.n (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).1
def pinnedPointOfReading (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) : PinT 𝒮 BdPt := fun _ p _ b => ∃ kap lam err, sidePt b = (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).upd kap lam err
end GlobalTheory.PlugPt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitAtPlacesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_equation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), SplitAt { v with N := N₁ } { o with M := M₁ } (PP.under (𝓞 D.host.F)) := by
  first | exact @_root_.GlobalTheory.SplitAtPlaces.splitAt_places_alt | exact _root_.GlobalTheory.SplitAtPlaces.splitAt_places_alt | (intros; apply _root_.GlobalTheory.SplitAtPlaces.splitAt_places_alt <;> assumption)
end
end


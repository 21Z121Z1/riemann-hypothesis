import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0569
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0521
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0594
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
import Formalism.PeriodIntegrals.Bundle0012
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0595
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTrueOfWitness
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.BundleLev

theorem lev_of_btw {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) (x : R3.TwIn O.ex) (y : Bl.BTw b x) :
    (pk (packB b)).Pg = x.R.Pg ∧ ∀ t, (pk (packB b)).xiH t = x.R.toLevCh.xiH (x.Y.tupT ((packB b).P.I.tup t)) := by
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y →
      k.B.Q.Rl.toRealDat.Pg = x.R.Pg ∧ ∀ t, k.B.Q.Rl.toRealDat.xiH t = x.R.toLevCh.xiH (x.Y.tupT (k.P.I.tup t)) := by
    intro k hk
    subst hk
    refine ⟨rfl, fun t => ?_⟩
    exact (congrArg x.R.toLevCh.xiH (x.Y.tupT_tup t)).symm
  exact key (Bl.rpkB b) y.eq

set_option maxHeartbeats 1000000 in

theorem lev_of_args {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) :
    x.R.Pg = (q.B.primes q.w.px).vGs ∧
      ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → x.R.toLevCh.xiH (x.Y.tupT μ) = q.w.I.xi μ := by
  have h := GlobalTheory.Mem.R3.twArgs_lev K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have e : a.x = x := eq_of_heq ax
  subst e
  exact ⟨eq_of_heq h.2.1, fun μ hμ => eq_of_heq (h.2.2.1 μ hμ).2⟩

set_option maxHeartbeats 1000000 in

theorem levTrue_packB : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → LevTrue (packB b) := by
  intro hL p K q c b hw
  have h1 := lev_of_btw b hw.x hw.y
  have h2 := lev_of_args q hw.x hw.a hw.ax
  have hPg : (pk (packB b)).Pg = (q.B.primes q.w.px).vGs := h1.1.trans h2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hPg]
    exact ColTest.isTypePlaces_vGs q.w.I q.w.l q.Z q.w.ok
  · intro PP
    rw [hPg]
    exact Iff.rfl
  · intro t
    exact (h1.2 t).trans (h2.2 _ (GlobalTheory.MiS.Check.used_all (packB b) t))

end GlobalTheory.Fam.BundleLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

abbrev Val (B : GlobalTheory.Mem.Base) : Type := VV B.fields.K B.wts.sgTrue

abbrev Frm (I : TC B X) (a : I.ι) : Type := (mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).EqFun

def val {I : TC B X} {a : I.ι} (φ : Frm I a) (d : RowPt (B.primes X) B.R I.sel (I.tup a)) : Val B := φ.1 d

def IsRes {I : TC B X} {a : I.ι} (φ : Frm I a) {V : Type} (x : V) : Prop :=
  ∃ ok : (mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).Ok,
    HEq ((mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a)).res ok φ) x

def HasVal {I : TC B X} (l : I.Laws) (u : B.Word) {a : I.ι} (φ : Frm I a) (G : (I.per l u a).Mt) : Prop :=
  ∀ p : (I.stX a).D (), (show (I.perIn u a).Mt B.fields.emb B.embLL from G).1 () p =
    MvPolynomial.map B.embLL (val φ (toRow I.sel (I.tup a) p.1.1)).1

def latOf (I : TC B X) (a : I.ι) (y : TC.GA B (B.R.N B.R.m - 1)) : RowPt (B.primes X) B.R I.sel (I.tup a) :=
  letI := GlobalTheory.Mem.Col2.starE B
  decoOf (F := B.fields.F) (E := B.fields.E) ∅ (rowSG (B.primes X) I.sel (I.tup a)) y

def IsUni (B : GlobalTheory.Mem.Base) (y : TC.GA B (B.R.N B.R.m - 1)) : Prop := y ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N B.R.m - 1)

def pairVal (B : GlobalTheory.Mem.Base) (z : (GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1)) → ℂ) (w : Val B) : ℂ :=
  pairB B.wts.sgTrue (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf B.wts.sgTrue)
    (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) z) (MvPolynomial.map B.embLL w.1)

variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

def RecVal (u : B.Word) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a) (G : (I.rec7 l Z).what₂.Amb a) : Prop :=
  (∀ h : a = (I.rec7 l Z).what₂.mu0, HasVal (a := I.mu0) l u (Eq.rec (motive := fun (ν : (I.rec7 l Z).what₂.Tup) _ => Frm I ν) φ h)
    (((I.rec7 l Z).eMt u).symm (Eq.rec (motive := fun ν _ => (I.rec7 l Z).what₂.Amb ν) G h))) ∧
  HasVal l u φ (((I.rec7 l Z).eMtTw u a).symm G)

variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

def ValEqv (c : Val B →ₛₗ[B.embLL] (pk W).cX.W) : Prop :=
  ∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
    GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = (pk W).cX.ρ γ.1 (c v)

def pkAt (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : (pk W).cX.W :=
  ((pk W).HX t).e ((pk W).jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h)

def PkVal (c : Val B →ₛₗ[B.embLL] (pk W).cX.W) : Prop :=
  ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
    ∀ h y, HasMat h y → IsUni B y → pkAt W t x h = c (val φ (latOf I (W.P.I.tup t) y))

def JVal (c : Val B →ₛₗ[B.embLL] (pk W).cX.W) (j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) : Prop :=
  ∀ w v, (pk W).prX (c w) v = pairVal B (j v) w

end GlobalTheory.TopVal

end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem period_single (l : I.Laws) (u : B.Word) (a : I.ι) (φ : Frm I a) (G : (I.per l u a).Mt) (hG : HasVal l u φ G)
    (c : (I.stX a).Cl) (z : (GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1)) → ℂ) (w : (I.per l u a).Wrow)
    (hw : w c = z) (hw' : ∀ c', c' ≠ c → w c' = 0) :
    (Nat.card ((I.stX a).Stab c) : ℂ) * (I.per l u a).period w G =
      pairVal B z (val φ (toRow I.sel (I.tup a) ((I.stX a).rep c).1.1)) := by
  letI := (I.perIn u a).clFin (l.per u a)
  have e : (I.per l u a).period w G = ∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' * pairB (K := ℂ) (I.perIn u a).sgT
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (w c')) ((I.perIn u a).rd B.fields.emb B.embLL G c') := by
    show ((∑ c' : (I.perIn u a).S'.Cl, _ : _ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) w) G = _
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    rfl
  rw [e, Finset.sum_eq_single (show (I.perIn u a).S'.Cl from c)]
  · have hs : (I.perIn u a).sgT = B.wts.sgTrue := rfl
    have h1 : (I.perIn u a).rd B.fields.emb B.embLL G c =
        MvPolynomial.map B.embLL (val φ (toRow I.sel (I.tup a) ((I.stX a).rep c).1.1)).1 := hG _
    haveI : Finite ((I.stX a).Stab c) := (l.per u a).step.fin_stab c.1 _
    have h2 : (Nat.card ((I.stX a).Stab c) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h3 : (Nat.card ((I.stX a).Stab c) : ℂ) * (I.perIn u a).wt c = 1 := mul_inv_cancel₀ h2
    rw [← mul_assoc]
    refine (congrArg (· * _) h3).trans ((one_mul _).trans ?_)
    subst hw
    exact congrArg _ h1
  · intro c' _ hc
    rw [hw' c' hc, map_zero, map_zero, LinearMap.zero_apply, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

set_option maxHeartbeats 1000000 in

theorem reads_of_val (hC : I.StdC l Z W.R.T.cols) (hW : GlobalTheory.AdForm.TwStd W) (u : B.Word)
    (j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a)
    (G : (I.rec7 l Z).what₂.Amb a) (hG : RecVal u a φ G)
    (f : SmT (pk W).MX →ₗ[ℂ] (GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → ℂ))
    (hf : ∀ h y (p : XPt (B.primes X) B.R I.sel (I.tup a)) v, HasMat h y → TC.PtOf y p →
      f v h = pairVal B (j v) (val φ (toRow I.sel (I.tup a) p))) :
    Reads W u j 1 a G f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    intro c v g hg
    have s := hC u
    rw [mul_one, hf g _ _ v hg (s.what₂.pt c)]
    have e := fun c' y => (s.eW ((W.R.T.cols.forms u).valP.eW.symm (Pi.single c (j v))) c' y y rfl).symm
    simp only [LinearEquiv.apply_symm_apply] at e
    refine (period_single l u I.mu0 φ _ (hG.1 rfl) c (j v) _ (funext fun y => (e c y).trans ?_)
      fun c' hc => funext fun y => (e c' y).trans ?_).symm
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
      rfl
  · obtain ⟨l0, t, he, ht, -, -, s⟩ := hW
    have key : ∀ (Tw : TwForms (I.rec7 l Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols Tw), Tw = I.tw l l0 Z → HEq t' t →
        ReadsG (t'.pt.cls u a h) (t'.pt.val u a h).eW j 1 (((I.rec7 l Z).eMtTw u a).symm G) f := by
      rintro _ t' rfl rfl
      intro c v g hg
      rw [mul_one, hf g _ _ v hg ((s.what₂ u a h).pt c)]
      have e := fun c' y => (s.eW u a h ((t'.pt.val u a h).eW.symm (Pi.single c (j v))) c' y y rfl).symm
      simp only [LinearEquiv.apply_symm_apply] at e
      refine (period_single l u a φ _ hG.2 c (j v) _ (funext fun y => (e c y).trans ?_)
        fun c' hc => funext fun y => (e c' y).trans ?_).symm
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
        rfl
    exact key _ _ he ht

end GlobalTheory.TopVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairCharacter
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

set_option maxHeartbeats 1000000 in

theorem centralRatio_stab_atT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTv
  have hm : 0 < D.R.m := by have := D.R.rS_two; omega
  obtain ⟨hsd, hfr⟩ := GlobalTheory.Fam.sdY_frames W hW 0 hm
  have hFG : ((pk W).ΛY 0).FG := hsd.1.fg
  have hkSt : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((pk W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkM : Moves (D.sp.Y 0) k ((pk W).ΛY 0) ((pk W).ΛY 0) (· = v) :=
    (GlobalTheory.StMoves.moves_iff_stabLoc _ _ hFG v k).2
      ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ _ hfr k).1 hkSt v)
  obtain ⟨c, hc⟩ := GlobalTheory.CenterScalar.center_mt_eq_smul_one D (D.sp.Y 0) z⁻¹ (Subgroup.inv_mem _ hzc)
  have hmul : ∀ g h : GA D (D.sp.Y 0), Formalism.L2.Theta.mt _ (g * h) = Formalism.L2.Theta.mt _ g * Formalism.L2.Theta.mt _ h :=
    fun g h => by simp [Formalism.L2.Theta.mt, map_mul]
  have hone : Formalism.L2.Theta.mt (D.sp.Y 0) 1 = 1 := by simp [Formalism.L2.Theta.mt, map_one]
  have h3 := GlobalTheory.T.placed_bessel_translate_vector W hW hr u f B hP a₀ a hA
  have h3' := GlobalTheory.T.placed_bessel_translate_vector W hW hr u' f' B' hP' a₀' a' hA'
  have h4 := GlobalTheory.T.placed_bessel_pair_vector W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' v hv hTv
  have h5 := GlobalTheory.coord_first_isotropic_ne_zero W.S.X W.Q.instEq hr
  generalize tOf f B a₀ a = t at he h3
  generalize tOf f' B' a₀' a' = t' at he h3'
  have hunit : IsUnit (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) :=
    ⟨⟨Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹, Formalism.L2.Theta.mt (D.sp.Y 0) t', by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩, rfl⟩
  have hkey : t'⁻¹ * z⁻¹ = k * t⁻¹ := by rw [he]; group
  have hMinv : Moves (D.sp.Y 0) z⁻¹ ((pk W).ΛY 0) ((pk W).ΛY 0) (· = v) := by
    intro y hy
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    refine GlobalTheory.LineUnit.smul_mem_latV_iff D (D.sp.Y 0) _ hsd.1 v _ h5 c _ hunit ?_ y hy
    intro b hb
    have h3b := h3 b
    have h3b' := h3' b
    have h4b := h4 b hb
    generalize hw : (fun i => b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = w at h3b h3b' h4b
    have hsupp : ∀ i, w i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => by
      rw [← hw]; exact Ideal.mul_mem_right _ _ hb
    have e1 : (fun i => c * (b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w := by
      rw [← hw, hc, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
    have s1 : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) k) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t⁻¹) w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul, hkey]
    have s2 := hkM _ (GlobalTheory.FinPl.KOpen.supp_mulVec _ _ t⁻¹ hsupp)
    rw [e1, s1, ← s2, h3b, h3b']
    exact h4b
  have hM := GlobalTheory.StMoves.moves_inv hMinv
  rw [inv_inv] at hM
  exact (GlobalTheory.StMoves.moves_iff_stabLoc (D.sp.Y 0) _ hFG v z).1 hM

end GlobalTheory.MiTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MemberCount

theorem rankMu_of_cols (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D) (hDu : StandardLattice.FactDuStar D)
    (u : D.what₂.Word) : GlobalTheory.Core.Rk.RankMu D u := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  have hr := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
    (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
  have hfin : Module.finrank ℂ (D.s.Cu u) = Module.finrank ℂ (D.mem u).A.Mu0 := (D.s_Cu u).finrank_eq
  unfold GlobalTheory.Core.Rk.RankMu GlobalTheory.Core.Rk.d0
  rw [hfin, hDu u]
  exact hr

theorem rankMu_of_bundle {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) (u : D.what₂.Word) :
    GlobalTheory.Core.Rk.RankMu D u :=
  rankMu_of_cols D O.ex.lev b.R.T.toTiedDataS.cols O.ex.duStar_def u

theorem member_rankMu : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  fun _ _ => RowE.of_all fun _ _ _ _ b _ _ _ u => rankMu_of_bundle b u

end GlobalTheory.Fam.MemberCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LinkedPins

set_option maxHeartbeats 4000000 in

theorem seeAt_twArgs {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : SeeAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 X h s) : SeeAt a.x.R.toRealDat a.x.F.lv2 X h s := by
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  refine ⟨hs.fin, ?_, ?_⟩
  · exact (hs.conj)
  · exact (hs.mat)

theorem setting_congr {D : D7} (M : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Prop)
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (e : F0 = F0') {P : SPack D F0} {P' : SPack D F0'} (hP : HEq P P')
    (h : M P'.X P'.inst) : M P.X P.inst := by
  subst e
  cases hP
  exact h

set_option maxHeartbeats 4000000 in

theorem realPins_of_seeAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} {x : TwIn ex} {Rc : Formalism.L2.RecT ex}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn x Rc S) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (sS : SRest P)
    (e : S = sS.toSTiesR Rc) (hC : x.R.C = Rc.T.n.cf) (hD : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i))
    (hPg : open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE))
    (hs : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS) : RealPins (realTOf y) := by
  subst e
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv := ((JIota.heq_iota_iff D P.X P.inst y.ιS).mp y.ιS_eq)
  refine realPins_realTOf _ _ _ _ _ _ _ _ ex x Rc _ y hC hD hPg hs.fin ?_ ?_
  · rw [hι]
    exact (hs.conj)
  · exact (hs.mat)

open Classical in

theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl

open Classical in

theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  have h : Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id := by
    funext P
    ext x
    exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x
  rw [h, Finset.image_id]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

set_option maxHeartbeats 4000000 in

theorem realPins_wit (q : WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c) (w : BWit q b) : RealPins (realTOf w.y.y) := by
  obtain ⟨x, a, ax, y, recPin, ⟨sP, sS, hP, -, e⟩, ⟨pt, -⟩, _⟩ := w
  cases ax
  obtain ⟨h1, h2, -⟩ := twArgs_lev _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hk := recPin.k.std
  have fd : ∀ V : Formalism.BasicNotions.TH.HSp (q.w.D q.Z), GlobalTheory.Mem.HostFrames.SignFrame V → IsFDiag V := fun V hV => by
    obtain ⟨d, -, h⟩ := hV.gram_eq (q.w.D q.Z).host.F
    exact ⟨d, h⟩
  have hWV := (GlobalTheory.Mem.HostFrames.frames_of_over K (q.w.st q.Z) q.x.isOver).2.1
  refine realPins_of_seeAt y.y sS e ?_ (fun i => ⟨fd _ (hWV i).1, fd _ (hWV i).2⟩) ?_ ?_
  · have hc : b.R.T.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst recPin.s.chr
    have hC : Top.Fr.at (q.w.st q.Z) q.w.I.C = Top.Fr.at (q.w.st q.Z) q.f := congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq
    exact (eq_of_heq h1).trans (hC.symm.trans hc.symm)
  · rw [image_congr hk.X_eq hk.seam hk.Pr]
    exact (eq_of_heq h2).trans (image_refl _ rfl _).symm
  · have ht : y.y.tS = q.sat.t := eq_of_heq pt
    have hcols : b.R.T.cols = q.x.col.C := recPin.s.cols
    rw [ht]
    exact seeAt_twArgs a sP.X sP.inst q.sat.t (setting_congr (D := (q.w.st q.Z).toD7)
      (fun X h => SeeAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 X h q.sat.t)
      (congrArg (fun C u => (C.forms u).to0) hcols) hP q.sat.see)

end GlobalTheory.Fam.LinkedPins

open GlobalTheory.MiS GlobalTheory.Fam in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Fam.realPins_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Formalism.IndefR.RealPins b.B.Q := by
  intro hL p K q c b w
  show (fun k : Bl.RPk b.R b.S => Formalism.IndefR.RealPins k.B.Q) (Bl.rpkB b)
  rw [w.y.eq]
  exact GlobalTheory.Fam.LinkedPins.realPins_wit q b w
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainOntoCuspFormsOfInnerProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_onto_cuspForms_of_innerProduct : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems | exact GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaStepVectorEqTupleCombOfLevelCombStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaStepVector_eq_tupleComb_of_levelComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ : WO S T → ℂ) (dG dQ : WO S T →₀ ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q → (∀ PP ∈ Pg, ∀ PP' ∈ Q, PP.under (𝓞 D.host.F) ≠ PP'.under (𝓞 D.host.F)) → (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) dG → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Q, p = PP.under (𝓞 D.host.F)) dQ → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj ∅ (fun _ => 1) f₀ (comb ψ S T dG f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ (comb ψ S T dG f₀)) := by
  first | exact @GlobalTheory.HalfProd.stepVec_of_prod | exact GlobalTheory.HalfProd.stepVec_of_prod | (intros; apply GlobalTheory.HalfProd.stepVec_of_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyPropertyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_family_property : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → GlobalTheory.MiTop.PlacedP (a.fam row col) a.d.B := by
  first | exact @GlobalTheory.FamPlaced.placed_of_true | exact GlobalTheory.FamPlaced.placed_of_true | (intros; apply GlobalTheory.FamPlaced.placed_of_true <;> assumption)
end


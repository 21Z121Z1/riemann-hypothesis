import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.Bundle0001
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTwLat
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0016

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.BasesAtSpec
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.UG
open scoped TensorProduct

namespace Formalism.MainNotions.G.KAat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E}

theorem latK_re {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y)
      (Lb.map (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) : (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) =
    (latK sp J a y Lb).map
      (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) : (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  subst h
  have e1 : J.reindex (finCongr rfl) (finCongr rfl) = J := by
    ext i j
    simp
  have e2 : Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) y = y := by
    apply Units.ext
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  rw [e1, e2, map_reE_rfl, map_reE_rfl]

end Re

section AtS

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def ptAt (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
      (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

set_option maxHeartbeats 1600000 in

theorem kerN_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN (i + 1) La).map
      ((reE (E := D.host.E) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 (i + 1) hi La)).toLinearMap.restrictScalars (𝓞 D.host.E)) =
    latK D.sp (gramN D (i + 1) hi) a (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La)
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb := by
  have e := latK_re (sp := D.sp) ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm (gramN D (i + 1) hi) a
    (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La) ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb
  have e0 : (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN (i + 1) La =
      (latK D.sp (gramN D (i + 1) hi) a (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La)
        ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb).map
      ((reE (E := D.host.E) ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    rw [← e]
    simp only [fdAtL, fdAt, fdOfCharts, cpAt, chAt, dif_pos hi]
    exact map_reE_rfl _ _
  rw [e0]
  exact map_reE_symm _ _ _

end AtS

section Spec

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D}

set_option maxHeartbeats 1600000 in

theorem basesAt_spec (i : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt v : Matrix _ _ _) := by
  obtain ⟨g, hg⟩ := (isLattice_iff _ ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt)).1 (hL v)
  exact Classical.epsilon_spec (p := fun g : GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) => (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt =
    colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _)) ⟨g, by rw [hg, colSpan_eq]⟩

theorem ptAt_spec (I : CmpJIn Tw u μ w h Lv) (i : ℕ) (hi : i + 1 ≤ D.R.m)
    (hG : ∀ β, LocGood (sigD D) (gramN D (i + 1) hi) ((I.at' i hi).st.loc β)) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
      (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La) ∧
    ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Classical.epsilon_spec (p := fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
      (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    ⟨_, (hG _).isPt_sec _ _, Subgroup.mul_mem _ ((hG _).yG_mem _) (SetLike.coe_mem _)⟩

end Spec

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TieStabKaAtAny
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
  {I : CmpJIn Tw u μ w h Lv}

theorem tieStab_kaAtAny [Fact (D.what₂.places.resChar w).Prime] (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh)
    (std) (vp) (unif) (eO) (eO_spec) (dG) (dG_spec) (om) (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (hU : DV.Used D μ) (hS0 : OrbitPlaces.Stab0 D) (j : ℕ) (hj : j ≤ D.R.m) : TieStabAt (Y := Y) u μ (kaAtAny X H Gt Ch hCh).cls j :=
  Formalism.L2.KerInert.SecondKernelStabilizers.stabilizer_any_level D c Tw u μ w h Fl Lv (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt Ch hCh std vp unif eO
    eO_spec dG dG_spec om Y hU hS0 j hj

def fillEmpty (hE : ∀ j, D.R.m < j → IsEmpty (Lv.comp j)) : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j :=
  fun j hj a => (hE j hj).elim a

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
  {I : CmpJIn Tw u μ w h Lv}

def tieAt (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) :
    TieAt c Tw u μ w h (chainAt H Gt) Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt where
  lab := labAt X H
  inp := I
  hyp := H
  ch := (kaAt X H Gt).cmp_K

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}

structure ChFam (E : Extra D L hT Gi Gl K Dx cX) where
  Lv : ∀ (_ : D.what₂.Tup) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Levels (Gl.Fl u w hg)
  I : ∀ (μ : D.what₂.Tup), DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp μ → CmpJIn E.tw u μ w hg (Lv μ u w hg)
  H : ∀ μ hU u w hg hq, CmpJHyp E.cmp (I μ hU u w hg hq)
  X : ∀ μ hU u w hg hq, LabIn (I μ hU u w hg hq)

open Classical in

def ChFam.ch {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Chain (F.Lv μ u w hg) :=
  if hh : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then chainAt (F.H μ hh.1 u w hg hh.2) hT else ⟨fun _ => 0⟩

theorem ChFam.ch_eq {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    F.ch μ u w hg = chainAt (F.H μ hU u w hg hq) hT := dif_pos ⟨hU, hq⟩

def ChFam.LC {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Gl.Fl u w hg), Chain Lv :=
  fun μ u w hg => ⟨F.Lv μ u w hg, F.ch μ u w hg⟩

def ChFam.ka {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    TwTie.KerAtMu D E.cmp E.tw u μ w hg (F.ch μ u w hg) :=
  kaAtAny (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) hT (F.ch μ u w hg) (by
    rw [F.ch_eq μ hU u w hg hq]
    exact (kaAt (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) hT).cmp_K)

def ChFam.tied {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0 : ∀ u, E.tw.e0 u D.what₂.mu0 = E.tw.eMu0 u 0 (Nat.zero_le _)) :
    TwTie.TwistedUnitaryExtraData E where
  LC := F.LC
  ker := fun μ hU u w hg hq => F.ka μ hU u w hg hq
  twisted_e0_at_mu0_eq_eMu0 := e0

theorem ChFam.tied_Lv {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((Pk.reW Gl (F.tied e0).LC).Yt μ).Lv u w hg = F.Lv μ u w hg := rfl

theorem ChFam.tied_Ch {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((Pk.reW Gl (F.tied e0).LC).Yt μ).Ch u w hg = F.ch μ u w hg := rfl

theorem ChFam.tied_cls {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    ((F.tied e0).ker μ hU u w hg hq).cls = clsAt (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) := rfl

theorem ChFam.tied_cmp {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ)
    (j : ℕ) (hj : j + 1 ≤ D.R.m) (x : ((E.tw.fm u μ).lat (j + 1)).V) :
    ((F.tied e0).ker μ hU u w hg hq).cmp (j + 1) x =
      ((F.I μ hU u w hg hq).at' j hj).st.cmpJ (E.cmp.embW u w hg) (((F.I μ hU u w hg hq).at' j hj).eps.symm x) :=
  kaAt_cmp (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) hT j hj x

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure AtIn where
  Fo : ∀ j (hj : j + 1 ≤ D.R.m), FormsIn (Tw.fm u μ) (j + 1) hj
  Lc : ∀ j (hj : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (Fo j hj).Ch

variable {X0 Tw u μ w h Lv}

def AtIn.st (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1)) :=
  stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h)

def AtIn.I (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) : CmpJIn Tw u μ w h Lv := inTw (Z.st Gt)

structure AtHyp (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  ties : ∀ j hj β, LocTiesR hj (Z.Fo j hj) (Z.Lc j hj) (c.embW u w h) β
  hypC : ∀ j hj β, HypTJC ((Z.Lc j hj).t β)
  ok : ∀ j hj, (Z.st Gt j hj).okW w
  twUnit : ∀ j hj β, (Z.st Gt j hj).TwUnit w β
  valIntN : ∀ j hj, (Z.st Gt j hj).ValIntN (c.embW u w h) w
  fin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses
  card : ∀ j (hj : j + 1 ≤ D.R.m), Fintype.card ((Tw.fm u μ).lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem AtHyp.hyp {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c (Z.I Gt) where
  core := fun j hj β => core_of_R hj K A.fl_t A.fill (A.ties j hj β)
  ok := A.ok
  twUnit := A.twUnit
  valIntN := A.valIntN
  iwF := fun j hj β => iwF_of hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) β
  fin := A.fin
  card := A.card

theorem AtHyp.chX {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (((Z.I Gt).at' j hj).st) :=
  chX_stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) (fun β => (A.ties j hj β).sameU) (fun β => (A.ties j hj β).frRat)
    (A.hypC j hj)

def AtHyp.lab {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (fl_m : Fl.mm = D.R.m) (c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv)
    (fill : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j) (rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j)
    (dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam) : LabIn (Z.I Gt) where
  onCh := fun _ _ => rfl
  chX := A.chX
  fl_t := A.fl_t
  fl_m := fl_m
  c0 := c0
  fill := fill
  rat := rat
  dgam := dgam

def kaAtZ {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (K : CmpTied D X0 T Gt c) (fl_m : Fl.mm = D.R.m)
    (c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv) (fill : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j)
    (rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j) (dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam) :
    TwTie.KerAtMu D c Tw u μ w h (chainAt (A.hyp K) Gt) :=
  kaAt (A.lab fl_m c0 fill rat dgam) (A.hyp K) Gt

end Formalism.MainNotions.G.KAat

end
end


import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsCharted1AtInTw
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Tw : TwForms D} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied D inQ} {Hc : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T Hc}
  {F : ∀ u, FormsTiedSym D u (Hc.Ch u) (Hc.chOf u)}
  {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def ClsCharted1 (T : Formalism.L2.Herm.TwChTied D inQ) (K : KerLabelsMu Tw u μ w h Lv) (ch : ∀ j, Lv.comp j → T.Ch u μ j) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → T.chOf u μ j (K.cls j a L) = ch j a

theorem yb_cls {K : KerLabelsMu Tw u μ w h Lv} {ch : ∀ j, Lv.comp j → T.Ch u μ j} (hC : ClsCharted1 T K ch) (h1 : 1 ≤ D.R.m - 1)
    (a : Lv.comp (D.R.m - 1)) (L : (Fl.Pj (D.R.m - 1)).Tup) (hL : (Fl.Pj (D.R.m - 1)).IsLatTup L) :
    T.yb u μ h1 (T.chOf u μ (D.R.m - 1) (K.cls (D.R.m - 1) a L)) = ybOf T ch h1 a := by
  unfold ybOf
  rw [hC (D.R.m - 1) h1 (Nat.sub_le _ _) a L hL]

def atInTw (W : TwFormsTiedS D Tw T J F) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)
    (Lc : ∀ j (_ : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (T.Ch u μ (j + 1))) : AtIn X0 Tw u μ w h Lv where
  Fo := fun j hj => formsInTw W u μ hμ j hj (dt j hj)
  Lc := Lc

variable (W : TwFormsTiedS D Tw T J F) (hμ : μ ≠ D.what₂.mu0)
  (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)
  (Lc : ∀ j (_ : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (T.Ch u μ (j + 1)))

def chTie_atInTw (Gt : GatTies D) : ChTie T ((atInTw W u μ hμ dt Lc).st Gt) where
  eCh := fun _ _ β => β
  chOf := fun _ _ _ => rfl

variable {W hμ dt Lc}

theorem clsCharted1_atInTw {Gt : GatTies D} {c : LatCmp D} (X : LabIn ((atInTw W u μ hμ dt Lc).I Gt))
    (H : CmpJHyp c ((atInTw W u μ hμ dt Lc).I Gt)) (ch : ∀ j, Lv.comp j → T.Ch u μ j)
    (hch : ∀ j (hj : j + 1 ≤ D.R.m) a, ch (j + 1) a = ((Lc j hj).eC.symm a).1) : ClsCharted1 T (labAt X H) ch := by
  intro j h1 hj a L hL
  cases j with
  | zero => omega
  | succ j =>
    rw [hch j hj]
    exact labAt_chOf (st := (atInTw W u μ hμ dt Lc).st Gt) X H j hj a L hL

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.KerLatRecTrivial
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.UG
open scoped TensorProduct

namespace Formalism.MainNotions.G.KAat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

theorem latAt_eq_of_kerN (fd : FData X D) (j : ℕ) (La Lb : X.Lt j) (v : X.Pl) (ρ : D.host.E →+* X.G.P.Qq v)
    (hk : fd.kerN j La = fd.kerN j Lb) (hf : fd.frM j La v = fd.frM j Lb v)
    (hWa : Formalism.L2.KerInert.RepTwLat.locSpan D (X.G.P.W v) ρ (fd.kerN j La) =
      (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)))
    (hWb : Formalism.L2.KerInert.RepTwLat.locSpan D (X.G.P.W v) ρ (fd.kerN j Lb) =
      (X.latAt v j Lb.2).map (((fd.frM j Lb v).mulVecLin).restrictScalars (X.G.P.W v)))
    (hM : Function.Injective (fd.frM j Lb v).mulVecLin) : X.latAt v j La.2 = X.latAt v j Lb.2 := by
  rw [hk, hWb, hf] at hWa
  exact (Submodule.map_injective_of_injective (f := ((fd.frM j Lb v).mulVecLin).restrictScalars (X.G.P.W v)) hM hWa).symm

end SlopeTestRemainingChoices

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} (I : CmpJIn ex.tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (t : KerEntTied ex) (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j)

def KerLatRec : Prop :=
  ∀ j (hj : j ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j),
    t.seam.lat ((t.rd u μ).N j (cls j La.1 La.2)) =
      ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j La).map
        ((reE (E := D.host.E) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j hj La)).toLinearMap.restrictScalars (𝓞 D.host.E))

variable {Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t cls}

theorem kerLatRec_const (H : KerLatRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t cls) (j : ℕ) (hj : j ≤ D.R.m)
    (La Lb : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j) (hc : cls j La.1 La.2 = cls j Lb.1 Lb.2) :
    (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j La = (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j Lb := by
  have h1 := H j hj La
  have h2 := H j hj Lb
  rw [hc, h2] at h1
  exact (Submodule.map_injective_of_injective (f := (reE (E := D.host.E)
    (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j hj La)).toLinearMap.restrictScalars (𝓞 D.host.E))
    (reE (E := D.host.E) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j hj La)).injective h1).symm

theorem kerLatRec_orbit (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (H : KerLatRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA.cls) (j : ℕ) (hj : j ≤ D.R.m)
    (c : Lv.comp j) (Lt : (Fl.Pj j).Tup) (hL : (Fl.Pj j).IsLatTup Lt) (γ : (Lv.lev j c).Γ) :
    (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j (c, (Lv.lev j c).smul γ Lt) =
      (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j (c, Lt) :=
  kerLatRec_const H j hj (c, (Lv.lev j c).smul γ Lt) (c, Lt)
    ((KA.cls_iff j hj c c Lt _ hL ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff _ _ γ Lt).2 hL)).2 ⟨rfl, γ, rfl⟩).symm

set_option maxHeartbeats 1600000 in

theorem frM_comp (i : ℕ) (c : Lv.comp (i + 1)) (Lt Lt' : (Fl.Pj (i + 1)).Tup) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) (c, Lt) v = (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) (c, Lt') v := by
  by_cases hi : i + 1 ≤ D.R.m
  · simp only [fdAtL, fdAt, fdOfCharts, cpAt, chAt, dif_pos hi]
    rfl
  · simp only [fdAtL, fdAt, fdOfCharts, cpAt, chAt, dif_neg hi]
    rfl

set_option maxHeartbeats 3200000 in

theorem kerLatRec_trivial (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (H : KerLatRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA.cls) (i : ℕ) (hi : i + 1 ≤ D.R.m)
    (ρ : ∀ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, D.host.E →+* (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v)
    (hW : ∀ La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1), ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).IsLatTup La'.2 → ∀ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl,
      Formalism.L2.KerInert.RepTwLat.locSpan D ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (ρ v) ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN (i + 1) La') =
        ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) La'.2).map
          ((((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) La' v).mulVecLin).restrictScalars ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v)))
    (hM : ∀ (La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl),
      Function.Injective ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) La' v).mulVecLin)
    (c : Lv.comp (i + 1)) (Lt : (Fl.Pj (i + 1)).Tup) (hL : (Fl.Pj (i + 1)).IsLatTup Lt) (γ : (Lv.lev (i + 1) c).Γ) :
    (Lv.lev (i + 1) c).smul γ Lt = Lt := by
  funext v
  exact latAt_eq_of_kerN (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) (i + 1) (c, (Lv.lev (i + 1) c).smul γ Lt) (c, Lt) v (ρ v)
    (kerLatRec_orbit KA H (i + 1) hi c Lt hL γ) (frM_comp i c _ Lt v)
    (hW (c, (Lv.lev (i + 1) c).smul γ Lt) ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff _ _ γ Lt).2 hL) v) (hW (c, Lt) hL v) (hM (c, Lt) v)

end Rec

end Formalism.MainNotions.G.KAat

end
end


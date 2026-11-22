import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartComparison
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.YbOfEqOfCls
import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle0002

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cast

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}

def castCls {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) (c : C.cls j) : C'.cls j := h ▸ c

theorem castCls_rfl {C : ColumnChain R ι hc} (j : ℕ) (c : C.cls j) : castCls (rfl : C = C) j c = c := rfl

theorem castCls_inj {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) : Function.Injective (castCls h j) := by
  subst h; exact fun _ _ h => h

theorem castCls_surj {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) : Function.Surjective (castCls h j) := by
  subst h; exact fun c => ⟨c, rfl⟩

theorem castCls_card {C C' : ColumnChain R ι hc} (h : C = C') (j : ℕ) (c : C.cls j) :
    Nat.card (C'.stab j (castCls h j c)) = Nat.card (C.stab j c) := by
  subst h; rfl

end Cast

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

structure LabIn (I : CmpJIn Tw u μ w h Lv) where
  onCh : ∀ j hj, (I.at' j hj).C = D.chTw u μ
  chX : ∀ j hj, ChX (I.at' j hj).st
  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m
  c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv
  fill : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j
  rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j
  dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam

variable {I : CmpJIn Tw u μ w h Lv}

def clsAt (X : LabIn I) (H : CmpJHyp c I) : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j
  | 0 => X.c0.cls
  | j + 1 => fun a L =>
    if hj : j + 1 ≤ D.R.m then castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else X.fill (j + 1) (by omega) a

theorem clsAt_succ (X : LabIn I) (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1)) (L : (Fl.Pj (j + 1)).Tup) :
    clsAt X H (j + 1) a L = castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) a L) := dif_pos hj

def levelChartElement (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1)) (L : (Fl.Pj (j + 1)).Tup) :
    GL (Fin (D.R.N (j + 1))) D.host.E := gam0 (S := (I.at' j hj).st) (H.core j hj) a L

def labAt (X : LabIn I) (H : CmpJHyp c I) : KerLabelsMu Tw u μ w h Lv where
  fl_t := X.fl_t
  fl_m := X.fl_m
  cls := clsAt X H
  cls_iff := fun j hj a a' L L' hL hL' => by
    cases j with
    | zero => exact X.c0.cls_iff a a' L L' hL hL'
    | succ j =>
      rw [clsAt_succ X H j hj, clsAt_succ X H j hj, (castCls_inj _ _).eq_iff]
      exact clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (X.chX j hj) a a' L L' hL hL'
  cls_surj := fun j hj x => by
    cases j with
    | zero => exact X.c0.cls_surj x
    | succ j =>
      obtain ⟨x0, rfl⟩ := castCls_surj (X.onCh j hj) (j + 1) x
      obtain ⟨a, L, hL, e⟩ := clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
      exact ⟨a, L, hL, by rw [clsAt_succ X H j hj]; exact congrArg _ e⟩
  stab_zero := X.c0.stab_zero
  stab_dvd := fun j hj a L hL => by
    cases j with
    | zero =>
      have e : Nat.card {γ : (Lv.lev 0 a).Γ // (Lv.lev 0 a).smul γ L = L} = 1 := X.c0.stab_zero a L hL
      rw [e]
      exact ⟨Nat.one_pos, one_dvd _⟩
    | succ j =>
      have e : Nat.card ((D.chTw u μ).stab (j + 1) (clsAt X H (j + 1) a L)) =
          Nat.card {γ : (Lv.lev (j + 1) a).Γ // (Lv.lev (j + 1) a).smul γ L = L} := by
        rw [clsAt_succ X H j hj, castCls_card]
        exact clsOf_card (S := (I.at' j hj).st) (H.core j hj) (X.chX j hj) a L hL
      rw [← e]
      exact ⟨Nat.card_pos, ((D.chTw u μ).dvd_DGam (j + 1) hj _).trans X.dgam⟩
  rat := X.rat
  stab_eq := fun j h1 hj a L hL => by
    cases j with
    | zero => omega
    | succ j =>
      rw [clsAt_succ X H j hj, castCls_card]
      exact clsOf_card (S := (I.at' j hj).st) (H.core j hj) (X.chX j hj) a L hL

abbrev chainAt (H : CmpJHyp c I) (Gt : GatTies D) : Chain Lv := chainMu (stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt).up

def kaAt (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) : TwTie.KerAtMu D c Tw u μ w h (chainAt H Gt) :=
  kerAtMu_cmpJ (labAt X H) H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt

def kaAtAny (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv)
    (hCh : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
      (stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt).up.cmp (j + 1) y = Ch.Kz j ((stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt).up.cmp j x)) :
    TwTie.KerAtMu D c Tw u μ w h Ch :=
  kerAtMu_any (labAt X H) H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt Ch hCh

theorem kaAt_cls (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) : (kaAt X H Gt).cls = clsAt X H := rfl

theorem kaAtAny_cls (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh) :
    (kaAtAny X H Gt Ch hCh).cls = clsAt X H := rfl

theorem kaAtAny_cmp_eq (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh) :
    (kaAtAny X H Gt Ch hCh).cmp = (kaAt X H Gt).cmp := rfl

theorem kaAt_cmp (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) (x : ((Tw.fm u μ).lat (j + 1)).V) :
    (kaAt X H Gt).cmp (j + 1) x = (I.at' j hj).st.cmpJ (c.embW u w h) ((I.at' j hj).eps.symm x) :=
  kerAtMu_cmpJ_cmp (labAt X H) H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt j hj x

theorem kaAt_chart (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1))
    (L : (Fl.Pj (j + 1)).Tup) (hL : (Fl.Pj (j + 1)).IsLatTup L) :
    ∃ c₀ : (I.at' j hj).C.cls (j + 1), (kaAt X H Gt).cls (j + 1) a L = castCls (X.onCh j hj) (j + 1) c₀ ∧
      (I.at' j hj).st.chOf c₀ = ((I.at' j hj).st.eC.symm a).1 ∧ IsCG (I.at' j hj).st a L c₀ (levelChartElement H j hj a L) :=
  ⟨_, clsAt_succ X H j hj a L, clsOf_chart (S := (I.at' j hj).st) (H.core j hj) a L hL,
    cg_spec (S := (I.at' j hj).st) (H.core j hj) a L hL⟩

theorem kaAt_sameChart (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a a' : Lv.comp (j + 1))
    (L L' : (Fl.Pj (j + 1)).Tup) (hL : (Fl.Pj (j + 1)).IsLatTup L) (hL' : (Fl.Pj (j + 1)).IsLatTup L')
    (e : (kaAt X H Gt).cls (j + 1) a L = (kaAt X H Gt).cls (j + 1) a' L') :
    ((I.at' j hj).st.eC.symm a).1 = ((I.at' j hj).st.eC.symm a').1 := by
  rw [((kaAt X H Gt).cls_iff (j + 1) hj a a' L L' hL hL').1 e |>.1]

theorem kaAt_pt (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (a0 : (I.at' j hj).st.cmpt β)
    (L : (Fl.Pj (j + 1)).Tup) (g : ∀ v, GL (Fin ((Fl.Pj (j + 1)).m + 1)) ((Fl.Pj (j + 1)).Qq v))
    (hL : ∀ v, L v = colSpan ((Fl.Pj (j + 1)).W v) (g v : Matrix (Fin ((Fl.Pj (j + 1)).m + 1)) (Fin ((Fl.Pj (j + 1)).m + 1))
      ((Fl.Pj (j + 1)).Qq v)))
    (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : ((I.at' j hj).st.loc β).IsPt a0 g x.1) :
    ∃ (hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L) = β)
      (κ : ((I.at' j hj).st.K β).lev.U),
      levelChartElement H j hj ((I.at' j hj).st.eC ⟨β, a0⟩) L ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) ∧
      x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (levelChartElement H j hj ((I.at' j hj).st.eC ⟨β, a0⟩) L) *
        (((I.at' j hj).st.K β).y ⟨_, hc⟩).1 * κ.1 := by
  have hLt : (Fl.Pj (j + 1)).IsLatTup L := isLatTup_of_bases (G := gatJ Lv (j + 1)) L g hL
  have hs := cg_spec (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L hLt
  have hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L) = β := by
    rw [hs.chart, Equiv.symm_apply_apply]
  obtain ⟨κ, e⟩ := hs.pt (H.core j hj) hc g hL x hx
  exact ⟨hc, κ, hs.mem, e⟩

theorem isCG_smul_at (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (a0 : (I.at' j hj).st.cmpt β)
    (L : (Fl.Pj (j + 1)).Tup) (hL : (Fl.Pj (j + 1)).IsLatTup L) (γ : (Lv.lev (j + 1) ((I.at' j hj).st.eC ⟨β, a0⟩)).Γ) :
    IsCG (I.at' j hj).st ((I.at' j hj).st.eC ⟨β, a0⟩) ((Lv.lev (j + 1) ((I.at' j hj).st.eC ⟨β, a0⟩)).smul γ L)
      (clsOf (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L)
      (((I.at' j hj).st.loc β).gamI a0 γ * levelChartElement H j hj ((I.at' j hj).st.eC ⟨β, a0⟩) L) :=
  (cg_spec (S := (I.at' j hj).st) (H.core j hj) ((I.at' j hj).st.eC ⟨β, a0⟩) L hL).smul (H.core j hj) γ

section OnTw

variable {st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))}

theorem labAt_chOf (X : LabIn (inTw st)) (H : CmpJHyp c (inTw st)) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1))
    (L : (Fl.Pj (j + 1)).Tup) (hL : (Fl.Pj (j + 1)).IsLatTup L) :
    (st j hj).chOf ((labAt X H).cls (j + 1) a L) = ((st j hj).eC.symm a).1 := by
  have e : (labAt X H).cls (j + 1) a L = clsOf (S := (st j hj)) (H.core j hj) a L := clsAt_succ X H j hj a L
  rw [e]
  exact clsOf_chart (S := (st j hj)) (H.core j hj) a L hL

theorem clsPt_labAt (X : LabIn (inTw st)) (H : CmpJHyp c (inTw st)) : ClsPt (labAt X H) st := by
  intro j hj β a L g hL c₀ γ₀ κ₀ hγ₀ hpt
  have e : (labAt X H).cls (j + 1) ((st j hj).eC ⟨β, a⟩) L = clsOf (S := (st j hj)) (H.core j hj) ((st j hj).eC ⟨β, a⟩) L :=
    clsAt_succ X H j hj _ L
  rw [e]
  exact clsOf_eq (S := (st j hj)) (H.core j hj) ⟨β, a, c₀.2, g, κ₀, rfl, hL, hγ₀, hpt⟩

end OnTw

section Yb

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
  {st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))}

structure ChTie (st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))) where
  eCh : ∀ j hj, (st j hj).Ch → T.Ch u μ (j + 1)
  chOf : ∀ j hj x, T.chOf u μ (j + 1) x = eCh j hj ((st j hj).chOf x)

variable {T}

theorem clsCharted_labAt (X : LabIn (inTw st)) (H : CmpJHyp c (inTw st)) (E : ChTie T st) (ch : ∀ j, Lv.comp j → T.Ch u μ j)
    (h0 : ∀ (a : Lv.comp 0) (L : (Fl.Pj 0).Tup), (Fl.Pj 0).IsLatTup L → T.chOf u μ 0 (X.c0.cls a L) = ch 0 a)
    (hch : ∀ j hj a, ch (j + 1) a = E.eCh j hj ((st j hj).eC.symm a).1) : ClsCharted T (labAt X H) ch := by
  intro j hj a L hL
  cases j with
  | zero => exact h0 a L hL
  | succ j => rw [E.chOf j hj, labAt_chOf X H j hj a L hL, hch j hj]

theorem ybOf_eq_labAt (X : LabIn (inTw st)) (H : CmpJHyp c (inTw st)) (ch : ∀ j, Lv.comp j → T.Ch u μ j)
    (h1 : 1 ≤ D.R.m - 1) (a a' : Lv.comp (D.R.m - 1)) (L L' : (Fl.Pj (D.R.m - 1)).Tup)
    (hL : (Fl.Pj (D.R.m - 1)).IsLatTup L) (hL' : (Fl.Pj (D.R.m - 1)).IsLatTup L')
    (he : (labAt X H).cls (D.R.m - 1) a L = (labAt X H).cls (D.R.m - 1) a' L') : ybOf T ch h1 a = ybOf T ch h1 a' := by
  have := ((labAt X H).cls_iff (D.R.m - 1) (Nat.sub_le _ _) a a' L L' hL hL').1 he
  rw [this.1]

end Yb

end Formalism.MainNotions.G.KAat

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ
section
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m)

section One

variable {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)
  {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad)

set_option maxHeartbeats 4000000 in

theorem compInj_locJ (hU : SameUlocJ hi S Uloc) : CompInj S (locJ hi t B) := by
  intro c c' δ hδ hoff
  have hδ0 : (reGL (rankN D (i + 1) hi) D.host.E).symm δ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram :=
    reGL_symm_mem_UJ (rankN D (i + 1) hi) _ _ _ (gramN_apply D (i + 1) hi) δ hδ
  have eδ : δ = reGL (rankN D (i + 1) hi) D.host.E ((reGL (rankN D (i + 1) hi) D.host.E).symm δ) :=
    (MulEquiv.apply_symm_apply _ _).symm
  set δ0 := (reGL (rankN D (i + 1) hi) D.host.E).symm δ with hδ0def
  have hz : ((t.yG c').1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1 ∈
      awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) := by
    rw [mem_awayG]
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (t.yG c').2) (bc_mem hδ0)) (t.yG c).2, fun w' hw' => ?_⟩
    have h1 := hoff w' hw'
    have e1 : ((locJ hi t B).yG c')⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (locJ hi t B).yG c =
        reGL (rankN D (i + 1) hi) _ (((t.yG c').1)⁻¹ *
          bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1) := by
      rw [eδ, map_mul, map_mul, map_inv, ← bc_reGL]
      rfl
    rw [e1, bc_reGL, hU w'] at h1
    exact (Subgroup.mem_map_iff_mem (f := (reGL (rankN D (i + 1) hi) _).toMonoidHom)
      (reGL (rankN D (i + 1) hi) _).injective).1 h1
  apply t.yG_bij.1
  show (Quotient.mk'' (t.yG c) : compG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w)) = Quotient.mk'' (t.yG c')
  have hz' := Subgroup.inv_mem _ hz
  refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, bc_mem hδ0⟩, Subgroup.mem_subgroupOf.2 ⟨δ0, hδ0, rfl⟩,
    ⟨_, ((mem_awayG _ _ _ _ _).1 hz').1⟩, Subgroup.mem_subgroupOf.2 hz', Subtype.ext ?_⟩
  show (t.yG c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1 *
    (((t.yG c').1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1)⁻¹
  group

end One

variable {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 4000000 in

theorem chX_stepInOf (Fo : FormsIn M (i + 1) hi) (Lc : LocIn X u w hg Lv i Fo.Ch)
    (pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau)
    (hU : ∀ β, SameUlocJ hi (Fo.K β).lev (Lc.Uloc β)) (hB : ∀ β, FrRatJ (Lc.t β) Lc.B) (hTc : ∀ β, HypTJC (Lc.t β)) :
    ChX (stepInOf hi Fo Lc pos) where
  hypC := fun (β : Fo.Ch) => locHypC_locJ hi (Lc.t β) Lc.B (Fo.K β).lev (hU β) (hB β) (hTc β)
  inj := fun (β : Fo.Ch) a => gamI_inj_locJ hi (Lc.t β) Lc.B a
  onto := fun (β : Fo.Ch) a => gamOnto_locJ hi (Lc.t β) Lc.B (Fo.K β).lev (hU β) a
  cinj := fun (β : Fo.Ch) => compInj_locJ hi (Lc.t β) Lc.B (Fo.K β).lev (hU β)

end Formalism.MainNotions.G.KAat

end
end


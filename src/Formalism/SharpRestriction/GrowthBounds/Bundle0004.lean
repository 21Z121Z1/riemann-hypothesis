import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GrowthBounds.Bundle0003

-- bundled from Formalism.SharpRestriction.GrowthBounds.KerTies
section
open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem

theorem Pj_rank {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) : (Fl.Pj j).m + 1 = NN G.P.m Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, NN]
  | succ j => simp only [Fills.Pj, Places.withWt, NN]; omega

theorem GIdx.ne_two {R : Ranks} {H : Host R} {T p : ℕ} (h : GIdx H T p) : p ≠ 2 := by
  have := h.2.1; omega

theorem GIdx.ne_d {R : Ranks} {H : Host R} {T p : ℕ} (h : GIdx H T p) : p ≠ H.d := by
  intro hd
  have hc : H.cls p = .inertClass := h.2.2.1
  unfold Host.cls primeClass at hc
  split_ifs at hc

def Pend.xForm {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (φ : Y.Frm j La La') (e : X.EA j ⊕ X.EA j) (z : X.ZA j) : Y.Kc :=
  ∑ z' : X.ZA j, MvPowerSeries.coeff (Finsupp.single z' 1) (X.coordZA Y.Kc j e) * Y.bc j La La' φ z' z

structure KerTies (D : D7) (Gt : GatTies D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime] (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D)
    (X : Sys (D.what₂.places.resChar w)) (Y : Pend X) where

  hG : X.G = D.gat u w h

  lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]

  iC : Y.Kc →+* ℂ_[D.what₂.places.resChar w]
  iC_int : ∀ x : Y.Kc, x ∈ Y.Oc ↔ ‖iC x‖ ≤ 1

  pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau

  iw : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v

  iw_lam : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E),
    iC (algebraMap X.G.Kf Y.Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) (iw v x)))) =
      Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) (if IsOddPos s then D.host.conj x else x))

  glob : ∀ j, X.Lt j → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)

  glob_adm : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.TaylorLogMetric.admitted D _ _ (glob j La) (glob (j + 1) La')

  glob_loc : ∀ j (La : X.Lt j), (X.Pj j).IsLatTup La.2 → ∀ v : X.Pl,
    X.latAt v j La.2 = Submodule.span (X.G.P.W v) {y | ∃ x ∈ glob j La, y = fun i => iw v (x i)}

  F : ∀ j, X.Lt j → X.Lt (j + 1) →
    MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]

  F_comb : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.TaylorLogMetric.IsComb D T e lam (glob j La) (glob (j + 1) La') (F j La La')

  ThF_eq : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (n : X.ZA j →₀ ℕ),
    iC (MvPowerSeries.coeff n (Y.ThF j La La')) =
      MvPowerSeries.coeff (n.mapDomain fun z : X.ZA j =>
        (pos ⟨z.1, z.2.1⟩, Fin.cast (Pj_rank X.Fl (j + 1)).symm z.2.2.2, Fin.cast (Pj_rank X.Fl j).symm z.2.2.1))
        (F j La La')

  iLL : D.what₂.LL →+* X.G.Kf
  iLL_w : ∀ x : D.what₂.LL, x ∈ intW D.what₂.places w ↔ iLL x ∈ Set.range (algebraMap X.G.O X.G.Kf)
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar),
    iC (algebraMap X.G.Kf Y.Kc (iLL x)) = lam ⟨D.what₂.embLL x, hx⟩

  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[iLL] X.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)
  cmp_int : ∀ j, j ≤ D.R.m → Submodule.span X.G.O
    (cmp j '' (((Tw.fm u (D.what₂.muAt w)).lat j).L : Set ((Tw.fm u (D.what₂.muAt w)).lat j).V)) = X.Int j
  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    cmp (j + 1) y = X.Kz j (cmp j x)

  fl_t : X.t = D.R.t
  fl_m : X.mm = D.R.m

  cls : ∀ j, X.Lt j → (D.chTw u (D.what₂.muAt w)).cls j
  cls_iff : ∀ j, j ≤ D.R.m → ∀ (La La' : X.Lt j), (X.Pj j).IsLatTup La.2 → (X.Pj j).IsLatTup La'.2 →
    (cls j La = cls j La' ↔ La.1 = La'.1 ∧ ∃ γ : (X.Lv.lev j La.1).Γ, La'.2 = (X.Lv.lev j La.1).smul γ La.2)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ La : X.Lt j, (X.Pj j).IsLatTup La.2 ∧ cls j La = x

  stab_eq : ∀ j, j ≤ D.R.m → ∀ La : X.Lt j, (X.Pj j).IsLatTup La.2 →
    X.stab j La = Nat.card ((D.chTw u (D.what₂.muAt w)).stab j (cls j La))

  val : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V → X.Lt j →
    MvPolynomial (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v) × (Fin ((X.Pj j).m + 1) × Fin ((X.Pj j).m + 1))) D.what₂.LL

  val_cmp : ∀ j, j ≤ D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (La : X.Lt j), (X.Pj j).IsLatTup La.2 →
    cmp j x La.1 La.2 = MvPolynomial.map iLL (val j x La)

  evC : ∀ j, MvPolynomial (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v) × (Fin ((X.Pj j).m + 1) × Fin ((X.Pj j).m + 1))) ℂ
    →ₗ[ℂ] ((D.chTw u (D.what₂.muAt w)).Y j → ℂ)

  val_emb : ∀ j, j ≤ D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V), ∀ La ∈ Y.Rep j,
    (Tw.fm u (D.what₂.muAt w)).emb j x (cls j La) = evC j (MvPolynomial.map D.what₂.embLL (val j x La))

def KerTies.kap {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) (j : ℕ) (z : X.ZA j) :
    D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1) :=
  (K.pos ⟨z.1, z.2.1⟩, Fin.cast (Pj_rank X.Fl (j + 1)).symm z.2.2.2, Fin.cast (Pj_rank X.Fl j).symm z.2.2.1)

structure KerTies.Frames {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) where
  cc : Ideal (𝓞 D.host.K)
  δ : ℂ
  hT : T = Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ
  g : Formalism.MainNotions.GL3Theta.G1 (D.what₂.places.resChar w)
  g_at : Formalism.MainNotions.GL3Theta.At D cc δ g
  g_lam : g.lam = K.lam

  th : PowerSeries (WW (D.what₂.places.resChar w))
  th_zero : PowerSeries.constantCoeff th = 0
  th_unit : IsUnit (PowerSeries.coeff 1 th)
  ep : (WW (D.what₂.places.resChar w))ˣ
  th_log : PowerSeries.subst
      (PowerSeries.map (K.iC.comp ((algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc).comp
        (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w))))) th)
      (PowerSeries.map (K.iC.comp (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc)) (logF (D.what₂.places.resChar w))) =
    PowerSeries.C (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
      (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (ep : WW (D.what₂.places.resChar w))))) * g.l

  be_tie : MvPowerSeries.subst
      ![MvPowerSeries.C (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
          (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (ep : WW (D.what₂.places.resChar w))))) *
          g.lg (MvPowerSeries.X (0 : Fin 2)),
        MvPowerSeries.C (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
          (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (ep : WW (D.what₂.places.resChar w))))) *
          g.lg (MvPowerSeries.X (1 : Fin 2))]
      (MvPowerSeries.map (K.iC.comp (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc)) Y.be) =
    g.be (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))

  okp : ∀ α : WW (D.what₂.places.resChar w), (sigW (D.what₂.places.resChar w))^[2] α = α →
    (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
        (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) α)),
      K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
        (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (sigW (D.what₂.places.resChar w) α)))) ∈
      Formalism.MainNotions.GL3Theta.OKp D K.lam

  yb : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)), Y.Frm j La La' → X.EA j ⊕ X.EA j →
    Formalism.MainNotions.GL3Theta.Idx D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) →
      ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w]
  yb_basis : ∀ j La La' (φ : Y.Frm j La La'), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.GL3Theta.BasisP D K.lam (Formalism.MainNotions.GL3Theta.YYp D K.lam (K.glob j La) (K.glob (j + 1) La')) (yb j La La' φ)
  yb_dual : ∀ j La La' (φ : Y.Frm j La La'), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.GL3Theta.DualIso (fun e => yb j La La' φ (Sum.inl e)) (fun e => yb j La La' φ (Sum.inr e))

  frameCompatibleExchange : ∀ j La La' (φ : Y.Frm j La La') (e e' : X.EA j ⊕ X.EA j),
    ∑ z : X.ZA j, K.iC (Y.xForm j La La' φ e z) *
      ((((g.C.u⁻¹ : ℂ_[D.what₂.places.resChar w]ˣ) : ℂ_[D.what₂.places.resChar w]) *
        (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
          (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w))
            (ep : WW (D.what₂.places.resChar w)))))⁻¹) * (yb j La La' φ e' (K.kap j z)).1) =
      if e = e' then 1 else 0

structure KerTies.Lift {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) where
  O : Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u (D.what₂.muAt w))
  rank_eq : ∀ j, (X.Pj j).m + 1 = D.R.N j
  p_notin : D.what₂.places.resChar w ∉ O.S
  lat_glob : ∀ j, j ≤ D.R.m → ∀ La ∈ Y.Rep j, ∀ x : Fin (D.R.N j) → D.host.E,
    x ∈ (O.lat j (K.cls j La)).1 ↔ (fun i => x (Fin.cast (rank_eq j) i)) ∈ K.glob j La
  F_Th : ∀ j, j < D.R.m → ∀ La ∈ Y.Rep j, ∀ La' ∈ Y.Rep (j + 1),
    ∀ n : (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →₀ ℕ,
    MvPowerSeries.coeff n (K.F j La La') =
      MvPowerSeries.coeff (n.mapDomain fun k => (k.1, Fin.cast (rank_eq (j + 1)) k.2.1, Fin.cast (rank_eq j) k.2.2))
        (Formalism.MainNotions.TaylorLogMetric.pSer D K.lam (O.Th j (K.cls j La) (K.cls (j + 1) La')))
  toFr : ∀ j, MvPolynomial (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v) × (Fin ((X.Pj j).m + 1) × Fin ((X.Pj j).m + 1))) ℂ
    →ₗ[ℂ] MvPolynomial (Formalism.MainNotions.GL3Theta.FrV D (D.R.N j)) ℂ

  dt : ℕ → D.what₂.Tau → ℕ
  evC_frm : ∀ j, j ≤ D.R.m → ∀ P (y : (D.chTw u (D.what₂.muAt w)).Y j),
    K.evC j P y * ∏ τ, (Matrix.det (O.frm j y τ)) ^ (dt j τ) = Formalism.MainNotions.GL3Theta.evFr D (toFr j P) (O.frm j y)

structure KerTies.Agrees {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv}
    {c : LatCmp D} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) : Prop where
  fl : HEq X.Fl Fl
  lv : HEq X.Lv Lv
  ch : HEq X.Ch Ch
  lam : K.lam = Kp.lam
  iLL : HEq K.iLL (c.embW u w h)
  glob : HEq K.glob (fun j (La : Lv.comp j × (Fl.Pj j).Tup) => Kp.glob j La.1 La.2)
  F : HEq K.F Kp.Th
  cmp : HEq K.cmp Kp.cmp
  cls : HEq K.cls (fun j (La : Lv.comp j × (Fl.Pj j).Tup) => Kp.cls j La.1 La.2)

end Formalism.MainNotions.FormalGroupSystem
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.KerTiesI
section
open Formalism.MainNotions.G Formalism.BasicNotions NumberField Formalism.MainNotions.TaylorLogMetric Classical

noncomputable section

namespace Formalism.MainNotions.G

def tvarOf (D : D7) {p d : ℕ} (Po : Pos D p d) {N N' : ℕ} (j : (Bool × HH D) × Fin N × Fin N') : TVar D Po N N' :=
  (((Equiv.ofBijective _ Po.bij).symm (tauPl D j.1)).2, (((Equiv.ofBijective _ Po.bij).symm (tauPl D j.1)).1, j.2))

def EntLiftSplit {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) : Prop :=
  ∃ (d : ℕ) (Po : Pos D (D.what₂.places.resChar w) d)
    (P : ∀ i, (D.chTw u μ).cls i → {v // v ∈ Po.V} → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E),
    (∀ i, i ≤ D.R.m → ∀ c v, LocBasisW D (posEmb D (E.lam w) Po.φ v.1 (0 : ZMod d)) (O.lat i c).1 (P i c v)) ∧
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u μ w i c c' = atLin (fun k (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
          c0 k.1 * lamC (E.lam w) (O.dgen k.1) * chg D (E.lam w) Po (P i c) (P (i + 1) c') k (tvarOf D Po j))
            (fun j => MvPowerSeries.X j) (pSer D (E.lam w) (O.Th i c c'))

def EntLiftC {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) : Prop :=
  ∃ P : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E,
    (∀ i, i ≤ D.R.m → ∀ c τ, OrthoBasisW D (tauEmb D (E.lam w) τ) (O.lat i c).1 (P i c τ)) ∧
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u μ w i c c' = atLin (fun k (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
          c0 k.1 * lamC (E.lam w) (O.dgen k.1) * chgB D (E.lam w) (P i c) (P (i + 1) c') k
            ((0 : ZMod 1), (tauPl D j.1, j.2))) (fun j => MvPowerSeries.X j) (pSer D (E.lam w) (O.Th i c c'))

def EntLift {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)
    (O : ∀ u μ, Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → D.what₂.places.resChar w ∉ (O u μ).S ∧
    (AllSplit D (D.what₂.places.resChar w) → EntLiftSplit E u μ (O u μ) w) ∧
    (IsFrobC D (D.what₂.places.resChar w) → EntLiftC E u μ (O u μ) w)

end Formalism.MainNotions.G
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SumRescaleTySTwo
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_X_pow_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) f := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  rw [PowerSeries.subst_comp_subst_apply hS hS]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]

theorem sum_rescale_tyS_two {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) (ha : a 1 = 0) :
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (tyS l fun s => (l : C) * a (s + 2)) := by
  have e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2) := by
    funext s
    cases s with
    | zero => simp [ha]
    | succ s => simp
  rw [← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]
  congr 1
  rw [← tyS_Vpow hl, e]

theorem sum_root_pow {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range l, (ζ ^ k) ^ (l ^ j) = (l : C) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  simp [h1]

theorem coeff_sum_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) (f : PowerSeries C) :
    PowerSeries.coeff (l ^ j) (∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) f) =
      (l : C) * PowerSeries.coeff (l ^ j) f := by
  rw [map_sum]
  simp only [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_root_pow hζ j hj]

section MM

variable {V : VF C}

theorem mmA_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mmA_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mmA_sum {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h

theorem mmA_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' hb ha

end MM

end SelfConjCharts

open SelfConjCharts in
theorem good_curve_closed : GoodCurveClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hxT : x ∈ X.TySet V g := hG.1.1
  have hx1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2

  have hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g := by
    have hF := (H g).Fm x hxT
    have h3 := (H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)
    have hsub := (H g).add _ _ hF ((H g).neg _ h3)
    convert hsub using 1
    funext i n
    cases i with
    | zero =>
      cases n with
      | inl c => simp [Vpow, Fs, const0, hx1 c]
      | inr q => simp [Vpow, Fs, const0, Cart.c0']
    | succ i => simp [Vpow, Fs, const0]
  have hyT' := X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT
  obtain ⟨γ, lam, hγ, hlam, hγ1, hγ2⟩ := id hxT
  obtain ⟨δ, -, hδ, -, hδ1, -⟩ := hyT'
  refine ⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]
  · intro i
    rw [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]
    exact mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)
  · intro q
    have hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) =
        PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) +
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inl c)) else 0) := by
      intro n
      have e := congrArg (PowerSeries.coeff n) (hγ2 q)
      simp only [map_add, map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero,
        smul_eq_mul] at e
      linear_combination e
    have hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1 := fun b => by
      simpa using coeff_tyS_pow hl2 b 1
    have hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2 := fun b => coeff_tyS_pow hl2 b 2
    have hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
        (V.l : C) * PowerSeries.coeff V.l f := fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f
    have hN2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
          (V.l : C) * PowerSeries.coeff (V.l ^ 2) f := fun f => coeff_sum_rescale hζ 2 (by norm_num) f
    have hl2pos : 0 < V.l ^ 2 := by positivity
    have hS1 : ∀ f : PowerSeries C,
        PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0 := fun f =>
      coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by
        have := Nat.le_of_dvd hl0 h
        nlinarith)
    have hS2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) =
          PowerSeries.coeff 1 f := fun f => by simpa using coeff_subst_X_pow hl2pos f 1
    refine ⟨hG.c0'_int q, ?_, ?_⟩
    · have e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q =
          -((V.l : C) * PowerSeries.coeff V.l (lam q)) := by
        unfold phi
        rw [map_sub, hS1, hN1, hA]
        simp only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']
        ring
      rw [e]
      exact MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))
    · have hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) =
          ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q) := by
        rw [coeff_alongCv_low le_rfl (fun j m hm => by
            obtain rfl : m = 0 := by omega
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]
        simp only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1,
          RawChart.sg1, Finset.mul_sum, zero_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) -
          (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) =
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> ring
      have e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) =
          (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) +
            -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q)) := by
        unfold phi
        rw [map_sub, hS2, hN2, hA, hB1]
        simp only [hT2]
        linear_combination key
      rw [e]
      refine mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))
      split_ifs with hm
      · exact mmA_zero
      · exact mmA_mul_int (hV2 c) (hB.hmis g c q hm)

end Formalism.L2.FormalSeriesBounds
end
end


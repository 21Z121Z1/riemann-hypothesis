import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0006
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0011
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0008

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.AsmIface
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

structure PC where
  CkLow : ℝ
  Ck6 : ℝ
  CfL : ℝ
  cLL : ℝ
  CnW : ℝ
  Crho : ℝ
  CDelG : ℝ
  CLw : ℝ
  Cj0 : ℝ
  Cw : ℝ
  cw : ℝ
  CDel : ℝ
  CCount : ℝ
  Ch0r : ℝ
  Ch0k : ℝ
  Ch0N : ℝ
  Cgap : ℝ
  CetaF : ℝ
  CY : ℝ
  CYL : ℝ
  Cpde : ℝ
  CccK : ℝ
  CF : ℝ

def PC.list (P : PC) : List ℝ :=
  [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
    P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
    P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF]

structure PTC where
  CP : ℝ
  eP : ℝ
  Cp : ℝ
  Cb : ℝ
  cTO : ℝ
  ChT : ℝ
  CbN : ℝ

def PTC.list (P : PTC) : List ℝ := [P.CP, P.eP, P.Cp, P.Cb, P.cTO, P.ChT, P.CbN]

structure FC where
  Ct : ℝ
  Cc : ℝ
  CT2 : ℝ
  CGam : ℝ
  Csz : ℝ
  Cr : ℝ
  CTu : ℝ

  Cdg : ℝ

  C5 : ℝ

  full : Prop
  GK : G.Consts
  cX : ExtraC
  P : PC
  T : PTC

def FC.PK (C : FC) : List ℝ := C.P.list

def FC.PT (C : FC) : List ℝ := C.T.list

def FC.cPre (C : FC) : List ℝ := [C.T.CP]

def FC.cOut (C : FC) : List ℝ := [C.Ct, C.Cc, C.CT2, C.P.CLw, C.P.Cj0, C.P.cw, C.P.CYL, C.P.Cpde, C.P.CccK,
  C.T.CP, C.T.Cp, C.T.eP, C.T.cTO, C.CTu, C.P.CetaF, C.P.Cpde]

def FC.cMid (C : FC) (CH : ℝ) : List ℝ := [CH, C.CGam, C.Csz, C.Csz, C.Csz, C.Csz, C.Csz,
  C.cX.err.g, C.GK.La, C.P.CF]

def FC.cLast (C : FC) : List ℝ := [C.P.CkLow, C.P.Ck6, C.P.CfL, C.P.cLL⁻¹, C.P.Crho, C.P.Crho, C.P.CDelG, C.P.Cw,
  C.P.CDel, C.P.CCount, C.P.Ch0r, C.P.Ch0k, C.P.Ch0N, C.P.Cgap, C.P.CY, C.T.Cb, C.T.ChT, C.T.CbN,
  C.GK.rho, C.GK.kII, C.GK.tII, C.GK.DII, C.GK.szII, C.GK.kII', C.GK.DI, C.GK.kappaThresholdOne,
  C.GK.kappaThresholdTwo, C.GK.kI, C.GK.CN, C.GK.CN, C.GK.CN, C.GK.CN]

def FC.Fixed (C : FC) : Prop :=
  C.GK.Pr1 = 1 ∧ C.GK.dl1 = 5 ∧ C.GK.dl2 = 4 ∧ C.cX.Ce = 1 ∧ C.cX.err.c6 = 12 ∧ C.cX.err.dig = 3 ∧ C.Cr = 1 ∧
    C.P.CnW = 10 ∧ 12 ≤ C.T.eP ∧ C.Ct = 401

def FC.Large (C : FC) (K : TransportedAlt) (CH : ℝ) : Prop :=
  (∀ c ∈ C.cPre, K.pre ≤ c) ∧ True ∧ (∀ c ∈ C.cMid CH, K.mid C.cOut ≤ c) ∧
    ∀ c ∈ C.cLast, K.last (C.cOut ++ C.cMid CH) ≤ c

structure Out where
  Cc : ℝ
  CT2 : ℝ
  CLw : ℝ
  Cj0 : ℝ
  cw : ℝ
  CYL : ℝ
  Cpde : ℝ
  CccK : ℝ
  Cp : ℝ
  eP : ℝ
  cTO : ℝ
  CTu : ℝ
  CetaF : ℝ
  Cdg : ℝ
  C5 : ℝ
  full : Prop

def FC.out (C : FC) : Out :=
  ⟨C.Cc, C.CT2, C.P.CLw, C.P.Cj0, C.P.cw, C.P.CYL, C.P.Cpde, C.P.CccK, C.T.Cp, C.T.eP, C.T.cTO, C.CTu, C.P.CetaF, C.Cdg,
    C.C5, C.full⟩

def bTopOf {D : D7} (L : SizeData₂ D) : ℝ :=
  L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ)

structure NumAt (C : FC) {D : D7} (L : SizeData₂ D) where
  params : ParameterChoice' D L
  params_K : parConsts params = C.PK
  CnW_eq : params.CnW = C.P.CnW
  parT : ParamsT D L params
  parT_K : [parT.CP, parT.eP, parT.Cp, parT.Cb, parT.cTO, parT.ChT, parT.CbN] = C.PT
  eP_eq : parT.eP = C.T.eP
  sizes : SizesAt L
  rho_le : G.rhoB D C.GK L.sc ≤ L.sc.x ^ (-2 : ℝ)
  CGam_eq : L.CGam = C.CGam
  Cc_eq : L.Cc = C.Cc
  Ct_eq : L.Ct = C.Ct
  secondConstant_eq : D.host.CT2 = C.CT2
  LaG_ge : L.sc.x ^ L.sc.eps ≤ L.LaG
  bT_le : ∀ t, (L.bT t : ℝ) ≤ bTopOf L

  ccK_top : D.host.ccK = ⊤
  g_le : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)
  pde_lt : (D.host.pde : ℝ) < L.sc.X' ∧ (D.host.pde' : ℝ) < L.sc.X'
  logFiveDepth_eq : L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
  Lw_eq : D.host.Lw = 10 * ⌈(C.Ct + 4) * Real.log L.sc.x⌉₊ + 2 * ⌈30 / L.sc.eps⌉₊ + 22
  cloud1 : ∀ τ τ', (D.hc τ).v = (D.hc τ').v
  win : (L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps)) ∧
    (Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ 2 * Real.sqrt (L.sc.x * L.sc.delta1)) ∧
    (L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ) ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps))

structure TiesAt (C : FC) {D : D7} (L : SizeData₂ D) (gatT : GatTies D) where
  Gx : G.Inst D L
  Gy : G.LatInst D
  supp_sat : ∀ w, ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n → w ∈ L.supp
  tw_supp : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp
  fills : ∀ w, G.ParametersFill Gx C.GK w
  lats0 : ∀ w u, G.VV Gx C.GK (G.aL L) (G.bL L) (D.what₂.places.resChar w) = ∅ →
    D.what₂.places.resChar w ≠ (D.mem u).A.T → L.lenMN u w = 0
  latTied : G.LatTied gatT Gx Gy
  drop_iff : ∀ p : ℕ, p.Prime → (p ∈ L.drop ↔ NoGain Gx C.GK C.Cr p ∧ ∀ u, p ≠ (D.mem u).A.T)

structure ExtraAt (C : FC) {D : D7} (L : SizeData₂ D) (gatT : GatTies D) (Gx : G.Inst D L) (Gy : G.LatInst D) where
  ties : Ties D
  X : DivX D
  nuDef : DV.NuDef D L
  nprimeDef : DV.NprimeDef D L
  rrDef : DV.RRDef D
  h_eq : ∀ u, D.div.h u = DV.hExpl6 D L X C.Csz u
  ex : Extra D L gatT Gx Gy C.GK X C.cX

def QDq (x eps C : ℝ) (q d : ℕ) : Prop :=
  BoundsAtX x eps C (GlobalTheoryTheory.psDir q) (8 * q * d) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧
  BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d)

def Boxq (x eps : ℝ) (q d : ℕ) : Prop :=
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir q) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (GlobalTheoryTheory.chDir d) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir d a) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps)
    (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d)

def Rowq (x eps : ℝ) (n q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < q ∧ (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧
  GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧
  Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

structure MoreH (sc : Scale) (C : FC) (Y : Σ R : Ranks, Host R) : Prop where
  t2 : Y.2.secondSet_card_lower_bound
  tt : sc.delta1 * Y.1.n / 2 ≤ (Y.2.TT.card : ℝ) ∧ (Y.2.TT.card : ℝ) ≤ 2 * sc.delta1 * Y.1.n
  qd : C.full → QDq sc.x sc.eps C.C5 Y.2.q Y.2.d
  boxes : C.full → Boxq sc.x sc.eps Y.2.q Y.2.d
  what₂ : C.full → Rowq sc.x sc.eps Y.1.n Y.2.q Y.2.d

@[ext] structure Shd where
  R : Ranks
  TTn : Finset ℕ
  T2 : Finset ℕ
  q : ℕ
  d : ℕ
  g : Fin 2 → ℕ
  pde : ℕ
  pde' : ℕ
  bits : ℕ → Bool
  LaG : ℝ
  etaSz : ℝ
  Sc : ℝ
  hP : ℕ → ℕ
  bs : ℕ → ℕ → ℕ
  off : ℕ → ℕ → ℝ
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

def Win (sc : Scale) (k : ℕ) (TTn : Finset ℕ) (bTop : ℝ) (a b : ℕ → ℤ) : Prop :=
  ∀ t ∈ TTn, (sc.a ≤ (a t : ℝ) ∧ (a t : ℝ) ≤ sc.a + sc.a / ((k : ℝ) * sc.x ^ (Scale.A / 2))) ∧
    sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ bTop

def Shd.bTop (S : Shd) (sc : Scale) : ℝ :=
  sc.b' + 2 * (S.R.n : ℝ) * sc.delta1 * sc.x ^ sc.eps * S.LaG * sc.b' / (S.R.k : ℝ)

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExistsLatInst
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.BasicNotions.Examples₂

section Base

variable {N : ℕ} [NeZero N]

theorem bsC_add_nsmul (h t : ZMod N) (i : ℕ) : bsC h (t + i • h) = bsC h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, bsC_step, ih]

theorem bsC_idem (h t : ZMod N) : bsC h (bsC h t) = bsC h t := by
  obtain ⟨i, hi⟩ := bsC_eq h t
  rw [hi, bsC_add_nsmul, ← hi]

theorem bsC_unique (h x x' : ZMod N) (i : ℕ) (e : bsC h x' = bsC h x + i • h) : bsC h x' = bsC h x := by
  rw [← bsC_idem h x', e, bsC_add_nsmul, bsC_idem]

end Base

section BaseA

variable {φ : Formalism.HC.Frame}

theorem bsA_add_nsmul (h t : φ.A) (i : ℕ) : bsA h (t + i • h) = bsA h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, bsA_step, ih]

theorem bsA_idem (h t : φ.A) : bsA h (bsA h t) = bsA h t := by
  obtain ⟨i, hi⟩ := bsA_eq h t
  rw [hi, bsA_add_nsmul, ← hi]

theorem bsA_unique (h x x' : φ.A) (i : ℕ) (e : bsA h x' = bsA h x + i • h) : bsA h x' = bsA h x := by
  rw [← bsA_idem h x', e, bsA_add_nsmul, bsA_idem]

end BaseA

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (sc : Scale) (eOf : ℕ → ℕ)

def baseB : D.what₂.Word → ℕ → Set (G.HH D) := fun _ p => {t | ∃ x, bsA (G.stepP D p) x = t}

def rOfB : D.what₂.Word → ℕ → ℕ := fun _ p => if (p : ℝ) < sc.p0 D.R.k then G.rG sc else 1

def recB : D7 := withGatCB D h0 (rOfB D sc) eOf (baseB D)

def tiesB : GatTies (recB D h0 sc eOf) := gatTiesCB D h0 (rOfB D sc) eOf (baseB D)

theorem stepP_of_gidx {T p : ℕ} (hg : GIdx D.host T p) : G.stepP D p = G.hP D p := by
  unfold G.stepP
  rw [if_neg]
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  have h2 : D.host.cls p = PrimeClass.signal := h
  rw [h1] at h2
  exact PrimeClass.noConfusion h2

theorem baseB_sep (u : D.what₂.Word) {T p : ℕ} (hg : GIdx D.host T p) :
    ∀ t ∈ baseB D u p, ∀ t' ∈ baseB D u p, ∀ i : ℕ, t' = t + i • G.hP D p → t' = t := by
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ i e
  rw [stepP_of_gidx D hg] at e ⊢
  exact bsA_unique _ _ _ i e

def posHypB {L : SizeData₂ (recB D h0 sc eOf)} (X : G.Inst (recB D h0 sc eOf) L) (hbs : X.bs = bsA) (hsc : L.sc = sc) :
    PosHyp (tiesB D h0 sc eOf) X where
  vOf := vOfCB D h0 (rOfB D sc) eOf (baseB D)
  inj := fun u w hg => by
    have h := vOfCB_injOn D h0 (rOfB D sc) eOf (baseB D) u w hg (baseB_sep D u hg)
    intro t ht t' ht' e
    have m : ∀ y, y ∈ G.reps X (D.what₂.places.resChar w) → y ∈ baseB D u (D.what₂.places.resChar w) := by
      intro y hy
      unfold G.reps at hy
      rw [hbs] at hy
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hy
      exact ⟨x, hx⟩
    exact h (m t ht) (m t' ht') e
  n_eq := fun u w hg t0 _ => withGatCB_n' D h0 (rOfB D sc) eOf (baseB D) u w hg _
  pos := fun u w hg t0 ht0 s => by
    have m : t0 ∈ baseB D u (D.what₂.places.resChar w) := by
      unfold G.reps at ht0
      rw [hbs] at ht0
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 ht0
      exact ⟨x, hx⟩
    exact gatTiesCB_pos D h0 (rOfB D sc) eOf (baseB D) u w hg (baseB_sep D u hg) m s
  r_eq := fun u w hg => by
    rw [hsc]
    rfl

theorem recB_M (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ((recB D h0 sc eOf).gat u w hg).M = ⊥ :=
  withGatC_M D h0 (rOfB D sc) eOf (fun u p => tau1P D.R.toFrame '' baseB D u p) u w hg

theorem recB_e (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((recB D h0 sc eOf).gat u w hg).e = eOf (D.what₂.places.resChar w) := rfl

theorem exists_latInst {L : SizeData₂ (recB D h0 sc eOf)} (X : G.Inst (recB D h0 sc eOf) L) (K : G.Consts) (hbs : X.bs = bsA)
    (hsc : L.sc = sc)
    (hf : ∀ j ∈ SizeData₂.lifts (recB D h0 sc eOf), ∀ (τ : (recB D h0 sc eOf).what₂.Tau) (z : Bool × G.HH (recB D h0 sc eOf)),
      ((recB D h0 sc eOf).eTau τ : (recB D h0 sc eOf).R.GG) = G.plGG (recB D h0 sc eOf) z →
        G.fill X (G.bL L) j z = wj (recB D h0 sc eOf) j τ)
    (hl : ∀ u w, L.lenMN u w = 0)
    (c : ℕ) (c_le : (c : ℝ) ≤ G.cG L) (hcl : L.Sc + (((recB D h0 sc eOf).R.k : ℝ) - 1) / 2 ≤ c)
    (hoff : ∀ u τ, ((recB D h0 sc eOf).eTau τ : (recB D h0 sc eOf).R.GG) ∉ (recB D h0 sc eOf).host.topPlaces →
      ∀ i : Fin (recB D h0 sc eOf).R.k,
        |((((recB D h0 sc eOf).hcW u τ).u i : ℚ) : ℝ) - ((((recB D h0 sc eOf).R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c)
    (hw1 : ∀ τ, (c : ℝ) ≤ wj (recB D h0 sc eOf) 1 τ - G.kaJ (recB D h0 sc eOf) 1) :
    ∃ Y : G.LatInst (recB D h0 sc eOf), G.LatTied (tiesB D h0 sc eOf) X Y ∧ ∀ w, G.LatticeLengthsAtPlace X Y K w :=
  ⟨(latHypOf (tiesB D h0 sc eOf) X (posHypB D h0 sc eOf X hbs hsc) c c_le hcl hoff hw1).latInst,
    (latHypOf (tiesB D h0 sc eOf) X (posHypB D h0 sc eOf X hbs hsc) c c_le hcl hoff hw1).latTied hf,
    fun w => sizeDataLat_of_M_bot X _ K (recB_M D h0 sc eOf) hl w⟩

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraRec
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

theorem Shape0.withTw (S : Shape0 D) (W : TwGap D) (hV : ∀ i j b k Q ψ, Subsingleton (W.nexp.MtV i j b k Q ψ))
    (hF : ∀ i j b, Subsingleton (W.nexp.Fm i j b)) : Shape0 (withTw D W) where
  mult := S.mult
  amb := S.amb
  mtL := S.mtL
  mj := S.mj
  ee0 := S.ee0
  rr := S.rr
  nu := S.nu
  lat := S.lat
  yTw := S.yTw
  clsTw := S.clsTw
  mtV := hV
  fmN := hF
  ll0 := S.ll0
  Ij0 := S.Ij0
  jw0 := S.jw0
  drows := S.drows
  dgam := S.dgam
  mink := S.mink
  loc := S.loc
  cls0 := S.cls0

def errXTw (X : ErrX D) (W : TwGap D) : ErrX (withTw D W) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong := X.piT_cong
  vPl := X.vPl
  vPl_inj := X.vPl_inj
  norm_mem_place_ideal := X.norm_mem_place_ideal

def LevGapD.withTw (G : LevGapD D) (W : TwGap D) : LevGapD (withTw D W) where
  lev := G.lev
  errX := errXTw G.errX W
  piG_lev := G.piG_lev
  piT_lev := G.piT_lev
  tau := G.tau
  tau_def := G.tau_def

section Rec

variable (D1 : D7) (W : TwGap D1) (large₂ : LevGapD D1) (h0 : ∀ u, Module.finrank ℂ (D1.mem u).A.Mu0 = 0)
  (rOf : D1.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (B : D1.what₂.Word → ℕ → Set (G.HH D1))

def recX : D7 := withGatCB (large₂.withTw W).recS h0 rOf eOf B

def recX_gatT : GatTies (recX D1 W large₂ h0 rOf eOf B) := gatTiesCB (large₂.withTw W).recS h0 rOf eOf B

theorem recX_shape (S : Shape0 D1) (hV : ∀ i j b k Q ψ, Subsingleton (W.nexp.MtV i j b k Q ψ))
    (hF : ∀ i j b, Subsingleton (W.nexp.Fm i j b)) : Shape (recX D1 W large₂ h0 rOf eOf B) :=
  Shape0.withGatB (D := (large₂.withTw W).recS) h0 rOf eOf B ((large₂.withTw W).shape0 (S.withTw W hV hF))

def recX_le : LevErr (recX D1 W large₂ h0 rOf eOf B) :=
  LevErr.withGatB (D := (large₂.withTw W).recS) h0 rOf eOf B (large₂.withTw W).le

theorem recX_ties (t : Ties (withTw D1 W)) : Ties (recX D1 W large₂ h0 rOf eOf B) :=
  { cdScale_tie := t.cdScale_tie
    dsig_tie := t.dsig_tie
    bu_def := t.bu_def
    tw_cover := t.tw_cover
    baseField_isGalois := t.baseField_isGalois
    ft_occ := t.ft_occ }

theorem recX_cover : NTw.TwCover (recX D1 W large₂ h0 rOf eOf B).ntw := W.cover

theorem recX_kapDef (h : DV.KapDef D1) : DV.KapDef (recX D1 W large₂ h0 rOf eOf B) := h

theorem recX_duStar (h : ∀ u, ((D1.mem u).A.duStar : ℝ) = StandardLattice.duStarU D1 u) :
    ∀ u, (((recX D1 W large₂ h0 rOf eOf B).mem u).A.duStar : ℝ) = StandardLattice.duStarU (recX D1 W large₂ h0 rOf eOf B) u := h

theorem recX_Dstar (h : D1.what₂.Dstar = StandardLattice.DstarD D1) :
    (recX D1 W large₂ h0 rOf eOf B).what₂.Dstar = StandardLattice.DstarD (recX D1 W large₂ h0 rOf eOf B) := h

theorem recX_e (u w h) : ((recX D1 W large₂ h0 rOf eOf B).gat u w h).e = eOf (D1.what₂.places.resChar w) := rfl

theorem recX_epTie {L : SizeData₂ (recX D1 W large₂ h0 rOf eOf B)} (X : G.Inst (recX D1 W large₂ h0 rOf eOf B) L)
    (h : X.ep = eOf) : EpTie X := fun u w hg => by rw [h]; rfl

theorem recX_gauge (hG : GaugeGap) : GaugeExists (recX D1 W large₂ h0 rOf eOf B).host (recX D1 W large₂ h0 rOf eOf B).sp :=
  hG _ _ _

def recX_served (hS : ServedGap) (hb : Function.Bijective D1.embE) (u : (recX D1 W large₂ h0 rOf eOf B).what₂.Word)
    (w : (recX D1 W large₂ h0 rOf eOf B).what₂.places.Pl)
    (h : GIdx (recX D1 W large₂ h0 rOf eOf B).host ((recX D1 W large₂ h0 rOf eOf B).mem u).A.T
      ((recX D1 W large₂ h0 rOf eOf B).what₂.places.resChar w)) :
    haveI : Fact ((recX D1 W large₂ h0 rOf eOf B).what₂.places.resChar w).Prime :=
      ⟨(recX D1 W large₂ h0 rOf eOf B).what₂.places.resChar_prime w⟩
    ServedEmb (recX D1 W large₂ h0 rOf eOf B) u w h :=
  (hS (large₂.withTw W).recS hb h0 rOf eOf (fun u p => tau1P D1.R.toFrame '' B u p) u w h).some

def recX_X (S : Shape0 D1) : DivX (recX D1 W large₂ h0 rOf eOf B) := divXExample _ S.drows S.mj

theorem recX_mjH (S : Shape0 D1) (j : ℕ) : Subsingleton ((recX_X D1 W large₂ h0 rOf eOf B S).MjH j).V :=
  inferInstanceAs (Subsingleton (zeroHLat _).V)

theorem recX_kapR (S : Shape0 D1) (e) : (recX_X D1 W large₂ h0 rOf eOf B S).kapR e = 1 := rfl

theorem recX_h (u) : (recX D1 W large₂ h0 rOf eOf B).div.h u = D1.div.h u := rfl

set_option maxHeartbeats 2000000 in
theorem recX_hVal (sc : Scale) (aT : D1.host.TT → ℤ) (η Sc dl C : ℝ) (u) :
    hVal (recX D1 W large₂ h0 rOf eOf B) sc aT η Sc dl C u = hVal D1 sc aT η Sc dl C u := rfl

end Rec

end Formalism.MainNotions.Inhab

end
end


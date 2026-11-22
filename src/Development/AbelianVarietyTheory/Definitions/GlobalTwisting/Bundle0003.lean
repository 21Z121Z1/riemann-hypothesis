import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0004
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
section
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

structure Pt (C : FC) : Type 1 where
  D : D7
  L : SizeData₂ D
  gatT : GatTies D
  ta : TiesAt C L gatT
  xa : ExtraAt C L gatT ta.Gx ta.Gy

abbrev PtProp : Type 1 :=
  ∀ (D : D7) (L : SizeData₂ D) (gatT : GatTies D) (Gx : G.Inst D L) (Gy : G.LatInst D) (K : G.Consts) (X : DivX D) (cX : ExtraC),
    Extra D L gatT Gx Gy K X cX → Prop

def Pt.Has {C : FC} (p : Pt C) (Q : PtProp) : Prop :=
  Q p.D p.L p.gatT p.ta.Gx p.ta.Gy C.GK p.xa.X C.cX p.xa.ex

def classOf (Q : PtProp) : FamClass := fun Fm =>
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Q (Fm.D x i) (Fm.L x i) (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.X x i) Fm.cX (Fm.ex x hx i)

def Pt.Chosen {C : FC} (p : Pt C) (C5 c6 Cb Cdg : ℝ) : Prop :=
  ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 ∧ ChThin_at p.D p.L.sc.x p.L.sc.eps c6 ∧
    ChProviso_at p.L 3 ∧ p.L.TuGe ∧
    (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧ FactDGam p.D Cdg

def Pt.Same {C : FC} (p p' : Pt C) : Prop :=
  p.D.R = p'.D.R ∧ p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val ∧ p.D.host.T2 = p'.D.host.T2 ∧
  p.D.host.q = p'.D.host.q ∧ p.D.host.d = p'.D.host.d ∧ p.D.host.g = p'.D.host.g ∧
  p.D.host.pde = p'.D.host.pde ∧ p.D.host.pde' = p'.D.host.pde' ∧
  p.L.etaSz = p'.L.etaSz ∧ p.L.Sc = p'.L.Sc ∧ (∀ l, (G.hP p.D l).val = (G.hP p'.D l).val) ∧
  (∀ (h t : G.HH p.D) (h' t' : G.HH p'.D), h.val = h'.val → t.val = t'.val → (p.ta.Gx.bs h t).val = (p'.ta.Gx.bs h' t').val) ∧
  (∀ j (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → p.ta.Gx.off j (false, t) = p'.ta.Gx.off j (false, t')) ∧
  p.ta.Gx.kapI = p'.ta.Gx.kapI ∧ p.ta.Gx.ep = p'.ta.Gx.ep ∧
  (∀ (t : p.D.host.TT) (t' : p'.D.host.TT), (t : p.D.R.A).val = (t' : p'.D.R.A).val →
    p.L.aT t = p'.L.aT t' ∧ p.L.bT t = p'.L.bT t') ∧
  p.D.host.QS = p'.D.host.QS ∧ artNum p.D.host.toHostRaw = artNum p'.D.host.toHostRaw ∧ p.D.host.rdE = p'.D.host.rdE

structure Kit (C : FC) (cD ch : ℝ) (s : Scale) : Type 1 where
  Ix : Type
  ne : Nonempty Ix
  pt : Ix → Pt C
  sc_eq : ∀ i, (pt i).L.sc = s
  val : ∀ i, Val C cD ch (pt i).L
  arith : ∀ i, HostArith (pt i).D.host
  same : ∀ i i', (pt i).Same (pt i')
  W : Type
  eW : ∀ i, (pt i).D.what₂.Word ≃ W
  eW_code : ∀ i i' u u', eW i u = eW i' u' → wordBits (pt i).D u = wordBits (pt i').D u'
  cover : ∀ i0 (u0 : ℕ), u0 < (pt i0).D.R.n → ∃ i, (pt i).D.host.u0.val = u0

def KitExW (la : ℝ) (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → ∃ (CT2 C8 : ℝ) (K0 : TransportedAlt), 1 ≤ C8 ∧
    ∀ C : FC, Std C → C.CT2 = CT2 → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2,
      ∃ C5 c6 Cb Cdg x0 : ℝ, 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ ∃ S : Scales la, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
        ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q ∧ (k.pt i).Chosen C5 c6 Cb Cdg

def KitEx (Q : PtProp) : Prop := ∃ la : ℝ, 1 < la ∧ KitExW la Q

def PtProp.and (Q Q' : PtProp) : PtProp := fun D L gatT Gx Gy K X cX ex =>
  Q D L gatT Gx Gy K X cX ex ∧ Q' D L gatT Gx Gy K X cX ex

def BoxesW (D : D7) (s : Scale) : Prop := ∃ Y : ℝ, PairWin s Y ∧ Boxes_at D Y s.eps ∧ GlobalTheoryTheory.BoxE D Y s.eps

def QDRowsW (D : D7) (s : Scale) : Prop := ∃ Y : ℝ, PairWin s Y ∧ QDRows_at D Y s.eps

def BoxesWF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧
    Boxes_at (Fm.D x i) Y eps ∧ GlobalTheoryTheory.BoxE (Fm.D x i) Y eps

def QDRowsWF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧ QDRows_at (Fm.D x i) Y eps

def ReqPt : PtProp := fun D L _ Gx _ K _ _ _ =>
  AuxBlock8.admW D L Gx K ∧ BoxesW D L.sc ∧ QDRowsW D L.sc

def PrimePt : PtProp := fun D L _ _ _ _ _ _ _ =>
  4 * D.host.Lw * D.host.T2.card ≤ D.R.n0 ∧
  (∀ i, ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧
    (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) ∧
  (D.host.pde % Nat.lcm 15 (D.host.QS * D.host.q * D.host.d) = 1 ∧ D.host.pde' % Nat.lcm 15 (D.host.QS * D.host.q * D.host.d) = 1) ∧
  ∃ q0 ∈ D.host.levelPrimes, q0.Prime ∧ q0 % (D.host.QS * D.host.q * D.host.d) = 1 ∧ Real.log q0 ≤ L.sc.L ∧ (q0 : ℝ) < L.sc.X' ∧
    q0 ≠ D.host.pde ∧ q0 ≠ D.host.pde' ∧ ∀ i, q0 ≠ D.host.g i

def TwPt : PtProp := fun D _ _ _ _ _ _ _ ex => LocalQuadraticParts.TWAt D ex.nch ex.xd

def AllReq : PtProp := ReqPt.and (PrimePt.and TwPt)

def ExFull (Q : PtProp) : Prop := KitEx (Q.and AllReq)

theorem Pt.has_and {C : FC} (p : Pt C) (Q Q' : PtProp) : p.Has (Q.and Q') ↔ p.Has Q ∧ p.Has Q' := Iff.rfl

theorem classOf_and (Q Q' : PtProp) {eps : ℝ} (Fm : FamP eps) : classOf (Q.and Q') Fm ↔ classOf Q Fm ∧ classOf Q' Fm :=
  ⟨fun h => ⟨fun x hx i => (h x hx i).1, fun x hx i => (h x hx i).2⟩, fun h x hx i => ⟨h.1 x hx i, h.2 x hx i⟩⟩

theorem KitExW.imp {la : ℝ} {Q Q' : PtProp} (h : KitExW la Q)
    (hQ : ∀ (C : FC) (cD ch : ℝ) (p : Pt C), Val C cD ch p.L → HostArith p.D.host → p.Has Q → p.Has Q') : KitExW la Q' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps h1 h2 h3 => ?_⟩
  obtain ⟨CT2, C8, K0, h8, h⟩ := h eps h1 h2 h3
  refine ⟨CT2, C8, K0, h8, fun C a b c d => ?_⟩
  obtain ⟨c1, h⟩ := h C a b c d
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨C5, c6, Cb, Cdg, x0, p5, p6, pb, S, h⟩ := h ch hch
  refine ⟨C5, c6, Cb, Cdg, x0, p5, p6, pb, S, fun s hs hx hm => ?_⟩
  obtain ⟨k, hk⟩ := h s hs hx hm
  exact ⟨k, fun i => ⟨hQ C cD ch _ (k.val i) (k.arith i) (hk i).1, (hk i).2⟩⟩

theorem KitEx.imp {Q Q' : PtProp} (h : KitEx Q)
    (hQ : ∀ (C : FC) (cD ch : ℝ) (p : Pt C), Val C cD ch p.L → HostArith p.D.host → p.Has Q → p.Has Q') : KitEx Q' :=
  let ⟨la, h1, h⟩ := h
  ⟨la, h1, h.imp hQ⟩

theorem ExFull.kitEx {Q : PtProp} (h : ExFull Q) : KitEx Q := KitEx.imp h fun _ _ _ _ _ _ hp => hp.1

theorem Pt.Same.refl {C : FC} (p : Pt C) : p.Same p := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl⟩
  · intro h t h' t' e1 e2
    rw [Formalism.HC.Frame.A.val_injective _ e1, Formalism.HC.Frame.A.val_injective _ e2]
  · intro j t t' e
    rw [Formalism.HC.Frame.A.val_injective _ e]
  · intro t t' e
    rw [Subtype.ext (Formalism.HC.Frame.A.val_injective _ e : t.1 = t'.1)]
    exact ⟨rfl, rfl⟩

theorem Pt.Same.weights {C : FC} {p p' : Pt C} (h : p.Same p') (t : p.D.host.TT) (t' : p'.D.host.TT)
    (e : (t : p.D.R.A).val = (t' : p'.D.R.A).val) : p.L.aT t = p'.L.aT t' ∧ p.L.bT t = p'.L.bT t' :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t t' e

theorem Pt.Same.QS_eq {C : FC} {p p' : Pt C} (h : p.Same p') : p.D.host.QS = p'.D.host.QS :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.Same.art_eq {C : FC} {p p' : Pt C} (h : p.Same p') :
    artNum p.D.host.toHostRaw = artNum p'.D.host.toHostRaw :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.Same.rd_eq {C : FC} {p p' : Pt C} (h : p.Same p') : p.D.host.rdE = p'.D.host.rdE :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Kit.cover_weights {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i0 : k.Ix) (u0 : ℕ)
    (hu : u0 < (k.pt i0).D.R.n) : ∃ i, (k.pt i).D.host.u0.val = u0 ∧
      ∀ (t : (k.pt i).D.host.TT) (t0 : (k.pt i0).D.host.TT),
        (t : (k.pt i).D.R.A).val = (t0 : (k.pt i0).D.R.A).val →
          (k.pt i).L.aT t = (k.pt i0).L.aT t0 ∧ (k.pt i).L.bT t = (k.pt i0).L.bT t0 := by
  obtain ⟨i, hi⟩ := k.cover i0 u0 hu
  exact ⟨i, hi, (k.same i i0).weights⟩

theorem Pt.disjoint_exceptional {C : FC} (p : Pt C) :
    Disjoint (Formalism.CyclotomicNorms.BB p.D.R.r (p.D.host.g 0)) (Formalism.CyclotomicNorms.BB p.D.R.r (p.D.host.g 1)) := p.D.ntypes.BB_disj

theorem Val.qdRows {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : QDRowsW D L.sc := h.host.1

theorem Val.mem_box {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) :
    G.aL L ∈ G.box D (G.winA D L.sc) ∧ G.bL L ∈ G.box D (G.winB D C.GK L.sc) := by
  classical
  constructor
  · refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ D.host.TT
    · simp only [G.aL, ht, dif_pos, if_true, G.winA, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
      exact L.aT_win ⟨t, ht⟩
    · simp [G.aL, ht]
  · refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ D.host.TT
    · simp only [G.bL, ht, dif_pos, if_true, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar]
      exact ⟨L.bT_ge ⟨t, ht⟩, h.La_eq ▸ h.bT_le ⟨t, ht⟩⟩
    · simp [G.bL, ht]

theorem Pt.has_reqPt_iff {C : FC} {cD ch : ℝ} (p : Pt C) (h : Val C cD ch p.L) :
    p.Has ReqPt ↔ AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) ∧ BoxesW p.D p.L.sc :=
  ⟨fun hp => ⟨hp.1.2.2, hp.2.1⟩, fun hp => ⟨⟨h.mem_box.1, h.mem_box.2, hp.1⟩, hp.2, h.qdRows⟩⟩

theorem classOf_reqPt {eps : ℝ} (Fm : FamP eps) (h : classOf ReqPt Fm) :
    (∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, AuxBlock8.admW (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK) ∧ BoxesWF Fm ∧ QDRowsWF Fm := by
  refine ⟨fun x hx i => (h x hx i).1, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, ⟨Fm.x1 + 1, fun x hx i => ?_⟩⟩
  · have hx' : Fm.x1 < x := by linarith
    have := (h x hx' i).2.1
    unfold BoxesW PairWin at this
    rwa [Fm.L_x x i hx', Fm.L_eps x i, Fm.L_J x i] at this
  · have hx' : Fm.x1 < x := by linarith
    have := (h x hx' i).2.2
    unfold QDRowsW PairWin at this
    rwa [Fm.L_x x i hx', Fm.L_eps x i, Fm.L_J x i] at this

theorem BoxesWF.boxesF {eps : ℝ} {Fm : FamP eps} (h : BoxesWF Fm) (hJ : Fm.J = 1) : BoxesF Fm := h

theorem QDRowsWF.qdRowsF {eps : ℝ} {Fm : FamP eps} (h : QDRowsWF Fm) (hJ : Fm.J = 1) : QDRowsF Fm := h

theorem boxesWF_iff {eps : ℝ} (Fm : FamP eps) : BoxesWF Fm ↔ BoxesF Fm := Iff.rfl

theorem qdRowsWF_iff {eps : ℝ} (Fm : FamP eps) : QDRowsWF Fm ↔ QDRowsF Fm := Iff.rfl

theorem mod_lcm_of_mod_mul {p N : ℕ} (hN : 0 < N) (h : p % (15 * N) = 1) : p % Nat.lcm 15 N = 1 := by
  have h1 : 1 < Nat.lcm 15 N := lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.lcm_pos (by norm_num) hN) (Nat.dvd_lcm_left 15 N))
  rw [← Nat.mod_mod_of_dvd p (Nat.lcm_dvd_mul 15 N), h, Nat.mod_eq_of_lt h1]

theorem mod_of_mod_lcm {p N : ℕ} (hN : 1 < N) (h : p % Nat.lcm 15 N = 1) : p % 15 = 1 ∧ p % N = 1 := by
  constructor
  · rw [← Nat.mod_mod_of_dvd p (Nat.dvd_lcm_left 15 N), h]
  · rw [← Nat.mod_mod_of_dvd p (Nat.dvd_lcm_right 15 N), h, Nat.mod_eq_of_lt hN]

theorem classOf_twPt {eps : ℝ} (Fm : FamP eps) (h : classOf TwPt Fm) : TwGood Fm := ⟨0, fun x _ hx i => h x hx i⟩

example {eps : ℝ} (Fm : FamP eps) : classOf (fun _ _ _ _ _ _ _ _ _ => True) Fm := fun _ _ _ => trivial

example {eps : ℝ} (Fm : FamP eps) : ¬ classOf (fun _ _ _ _ _ _ _ _ _ => False) Fm := fun h => by
  obtain ⟨x, -, hx, -, ⟨i⟩⟩ := Fm.toFamCore.exists_pt 0
  exact h x hx i

example {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) :
    ∃ i i' : k.Ix, (k.pt i).D.host.u0.val ≠ (k.pt i').D.host.u0.val := by
  obtain ⟨i0⟩ := k.ne
  have h2 : 1 < (k.pt i0).D.R.n := by
    have h1 : 1 < 2 ^ ((k.pt i0).D.R.e + 2) := Nat.one_lt_two_pow (by omega)
    have h3 := (h1.trans_le (Nat.le_of_dvd (k.pt i0).D.host.QS_pos (k.pt i0).D.host.tower_dvd)).trans_le (k.pt i0).D.host.QS_le
    by_contra hn
    have h4 : (k.pt i0).D.R.n ^ 2 ≤ 1 := pow_le_one₀ (Nat.zero_le _) (by omega)
    omega
  obtain ⟨i, hi⟩ := k.cover i0 0 (by omega)
  obtain ⟨i', hi'⟩ := k.cover i0 1 h2
  exact ⟨i, i', by omega⟩

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsIntegralPendingObjectSymmetricFormsLevel
section
noncomputable section

namespace GlobalTheory.LvT.PendExample

open Formalism.BasicNotions Classical NumberField GlobalTheory.MemberTorsor
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

section Span
variable (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

def GSpan : AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : 𝓞 D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL (r : D.what₂.LL) • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

variable {D lam}

theorem gspan_smul (d : 𝓞 D.what₂.LL) {p} (hp : p ∈ GSpan D lam) : D.what₂.embLL (d : D.what₂.LL) • p ∈ GSpan D lam := by
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r, f, hf, rfl⟩ := hq
    exact AddSubgroup.subset_closure ⟨d * r, f, hf, by rw [smul_smul, ← map_mul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

variable (lam) in

def idl (G : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) : Submodule (𝓞 D.what₂.LL) (Unit → D.what₂.LL) where
  carrier := {x | D.what₂.embLL (x ()) • G ∈ GSpan D lam}
  add_mem' {a b} ha hb := by
    show D.what₂.embLL (a () + b ()) • G ∈ GSpan D lam
    rw [map_add, add_smul]; exact add_mem ha hb
  zero_mem' := by
    show D.what₂.embLL 0 • G ∈ GSpan D lam
    rw [map_zero, zero_smul]; exact zero_mem _
  smul_mem' d a ha := by
    show D.what₂.embLL ((d : D.what₂.LL) * a ()) • G ∈ GSpan D lam
    rw [map_mul, mul_smul]; exact gspan_smul d ha

variable {g : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ}

end Span

section Lat
variable (K : Type) [Field K] [NumberField K] [StarRing K] (κ : Type) [Fintype κ] [DecidableEq κ]

@[reducible] def sLat (a : ℝ) (L : Submodule (𝓞 K) (κ → K)) : HLat K where
  V := κ → K
  ι := κ
  b := Pi.basisFun K κ
  X := fun _ => ((a : ℂ)⁻¹) • 1
  L := L

variable {K κ}

theorem sLat_good {a : ℝ} (ha : a ≠ 0) {L : Submodule (𝓞 K) (κ → K)} (h1 : L.FG)
    (h2 : Submodule.span K (L : Set (κ → K)) = ⊤) : (sLat K κ a L).Good := by
  refine ⟨fun v => ?_, h1, h2⟩
  show IsUnit (Matrix.det (((a : ℂ)⁻¹) • (1 : Matrix κ κ ℂ)))
  have : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  simp [this]

theorem sLat_norm {a : ℝ} (ha : a ≠ 0) (L : Submodule (𝓞 K) (κ → K)) (σ : K →+* ℂ) (x : κ → K) :
    (Formalism.HermitianLatticesTheory.majAt (sLat K κ a L).b (sLat K κ a L).X (InfinitePlace.mk σ) x x).re =
      (∑ c, (((a ^ 2 : ℝ) : ℂ) • ipUnit) (stdEmb κ σ x c) (stdEmb κ σ x c)).re := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hi : (((a : ℂ)⁻¹) • (1 : Matrix κ κ ℂ))⁻¹ = (a : ℂ) • (1 : Matrix κ κ ℂ) :=
    Matrix.inv_eq_left_inv (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha']; simp)
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h1 : ((sLat K κ a L).X (InfinitePlace.mk σ))⁻¹.mulVec
      (Formalism.HermitianLatticesTheory.vecAt (sLat K κ a L).b (InfinitePlace.mk σ) x) c =
      a * (InfinitePlace.mk σ).embedding (x c) := by
    show ((((a : ℂ)⁻¹) • (1 : Matrix κ κ ℂ))⁻¹.mulVec _) c = _
    rw [hi, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [h1]
  show (starRingEnd ℂ _ * _).re = (((a ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (σ _) * σ _)).re
  rw [Complex.conj_mul', Complex.conj_mul', norm_mul, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  push_cast
  rw [mul_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast
  rfl

end Lat

section Chain
variable (D : D7) (u : D.what₂.Word) (T : ℕ) [Fact T.Prime]

def mk (sg : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Submodule (𝓞 D.what₂.LL) (Unit → D.what₂.LL)) (h1 : L.FG)
    (h2 : Submodule.span D.what₂.LL (L : Set (Unit → D.what₂.LL)) = ⊤) (be : D.what₂.Tau → ℝ) (hbe : ∀ τ, 0 ≤ be τ) :
    Ch D u where
  C := chain D.R D.what₂.Tau (D.hcW u) T
  A := atT D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau
  P := period D.R D.what₂.Tau (D.hcW u) T
  fm := { forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places with
    sg := sg
    ipV := fun _ _ => ((a ^ 2 : ℝ) : ℂ) • ipUnit
    lat := fun _ => sLat D.what₂.LL (D.what₂.Tau → (ZMod T)ˣ) a (stdLat D.what₂.LL _).L
    lat_good := fun _ => sLat_good ha (stdLat_good D.what₂.LL _).2.1 (stdLat_good D.what₂.LL _).2.2
    emb := fun _ => stdEmb _ D.what₂.embLL
    emb_basis := fun _ => stdEmb_basis _ D.what₂.embLL
    emb_norm := fun i x => by
      rw [sLat_norm ha]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      have : (chain D.R D.what₂.Tau (D.hcW u) T).wt i c = 1 := by
        show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ = 1
        simp
      rw [this, one_mul]
    rhoT_lat := (forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places).rhoT_lat
    Bw := (forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places).Bw
    Bw_span := (forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places).Bw_span
    ipP := ((((b ^ 2 : ℝ) : ℂ) • ipUnit).comp (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Unit → ℂ) ())).compl₂
      (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Unit → ℂ) ())
    ptLat := sLat D.what₂.LL Unit b L
    ptLat_good := sLat_good hb h1 h2
    ptEmb := stdEmb _ D.what₂.embLL
    ptEmb_basis := stdEmb_basis _ D.what₂.embLL
    ptEmb_norm := fun x => by
      rw [sLat_norm hb, Fintype.sum_unique]
      rfl
    beOn := be
    beOn_nonneg := hbe }

def base (sg : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1)) : Ch D u :=
  mk D u T sg 1 1 one_ne_zero one_ne_zero (stdLat D.what₂.LL Unit).L (stdLat_good D.what₂.LL _).2.1
    (stdLat_good D.what₂.LL _).2.2 0 fun _ => le_rfl

end Chain

theorem nfAll_pos {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ≠ 0) : 0 < (nfAll l p p).re := by
  unfold nfAll
  simp only [fockF_self_eq (extremal ℂ n _)]
  rw [← Complex.ofReal_prod, Complex.div_ofReal_re]
  refine div_pos (fockF_self_pos hp) (Finset.prod_pos fun τ _ => ?_)
  have := fockF_self_pos (f := extremal ℂ n (l τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (l τ).natW)
  rwa [fockF_self_eq, Complex.ofReal_re] at this

def frameL {n : ℕ} (l : DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  detPow ℂ n g l.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap

def tailW {N : ℕ} (l : DomWeight N) : DomWeight (N - 1) where
  w i := l.w ⟨i.1 + 1, by omega⟩
  anti _ _ h := l.anti (Nat.succ_le_succ h)

def tailSg (D : D7) (u : D.what₂.Word) : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => tailW (Examples₂.lamOf (D.hcW u τ) D.R.m)

end GlobalTheory.LvT.PendExample
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.TorIsoId
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open NumberField

def Stable (K : IntermediateField ℚ ℂ) (L : PeriodPair) : Prop :=
  ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice

def Tor (q : ℕ) (L : PeriodPair) : Set ℂ := {z | ∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ (m : ℂ) * z ∈ L.lattice}

def Maps (μ : ℂ) (L L' : PeriodPair) : Prop := ∀ z ∈ L.lattice, μ * z ∈ L'.lattice

def idx (μ : ℂ) (L L' : PeriodPair) : ℕ :=
  (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft μ)).relIndex L'.lattice.toAddSubgroup

def Incong (L : PeriodPair) (S : Finset ℂ) : Prop := ∀ z ∈ S, ∀ w ∈ S, z - w ∈ L.lattice → z = w

structure TorIso (K : IntermediateField ℚ ℂ) (q : ℕ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop where
  maps : ∀ z ∈ Tor q L, θ z ∈ Tor q L'
  add : ∀ z ∈ Tor q L, ∀ w ∈ Tor q L, θ (z + w) - θ z - θ w ∈ L'.lattice
  ker : ∀ z ∈ Tor q L, θ z ∈ L'.lattice ↔ z ∈ L.lattice
  surj : ∀ w ∈ Tor q L', ∃ z ∈ Tor q L, θ z - w ∈ L'.lattice
  lin : ∀ (a : 𝓞 K), ∀ z ∈ Tor q L, θ (((a : K) : ℂ) * z) - ((a : K) : ℂ) * θ z ∈ L'.lattice

def Cnt (K : IntermediateField ℚ ℂ) (q : ℕ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop :=
  ∀ (μ : ℂ) (β : 𝓞 K), μ ≠ 0 → β ≠ 0 → Maps μ L L' →
    (∀ z ∈ Tor q L, μ * z - θ (((β : K) : ℂ) * z) ∈ L'.lattice) ∨
    (∀ z ∈ Tor q L, μ * z + θ (((β : K) : ℂ) * z) ∈ L'.lattice) ∨
    ∀ S : Finset ℂ, Incong L S → (∀ z ∈ S, z ∈ Tor q L ∧ ((β : K) : ℂ) * z ∉ L.lattice ∧
        (μ * z - θ (((β : K) : ℂ) * z) ∈ L'.lattice ∨ μ * z + θ (((β : K) : ℂ) * z) ∈ L'.lattice)) →
      S.card ≤ 2 * (idx μ L L' + idx ((β : K) : ℂ) L L)

structure Transp (σ : ℂ ≃+* ℂ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop where
  g2 : L'.g₂ = σ L.g₂
  g3 : L'.g₃ = σ L.g₃
  add : ∀ z w, θ (z + w) - θ z - θ w ∈ L'.lattice
  ker : ∀ z, θ z ∈ L'.lattice ↔ z ∈ L.lattice
  surj : ∀ w, ∃ z, θ z - w ∈ L'.lattice
  wp : ∀ z, z ∉ L.lattice → L'.weierstrassP (θ z) = σ (L.weierstrassP z)
  wp' : ∀ z, z ∉ L.lattice → L'.derivWeierstrassP (θ z) = σ (L.derivWeierstrassP z)

def Good (W : ValuationSubring ℂ) (L : PeriodPair) : Prop :=
  L.g₂ ∈ W ∧ L.g₃ ∈ W ∧ (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W

def web (L : PeriodPair) (z : ℂ) : ℂ := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP z

def jj (L : PeriodPair) : ℂ := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

def allWeber (K : IntermediateField ℚ ℂ) (n : ℕ) : Set ℂ :=
  {w | ∃ L : PeriodPair, Stable K L ∧ w ∈ GlobalTheory.FieldSize.weberSet L n}

theorem torIso_id (K : IntermediateField ℚ ℂ) (q : ℕ) (L : PeriodPair) : TorIso K q L L id where
  maps := fun _ h => h
  add := fun z _ w _ => by simp
  ker := fun _ _ => Iff.rfl
  surj := fun w h => ⟨w, h, by simp⟩
  lin := fun a z _ => by simp

theorem transp_id (L : PeriodPair) : Transp (RingEquiv.refl ℂ) L L id where
  g2 := rfl
  g3 := rfl
  add := fun z w => by simp
  ker := fun _ => Iff.rfl
  surj := fun w => ⟨w, by simp⟩
  wp := fun _ _ => rfl
  wp' := fun _ _ => rfl

end GlobalTheory.CMRam
end
end


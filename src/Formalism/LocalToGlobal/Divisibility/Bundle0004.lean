import Mathlib
import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
import Formalism.LocalToGlobal.KernelLattices.Bundle0003
import Formalism.LocalToGlobal.Columns.GoodXgE
import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Formalism.LocalToGlobal.Columns.Bundle0047
import Formalism.LocalToGlobal.Divisibility.TwistedPlaceEtaSumLeExtended

-- bundled from Formalism.LocalToGlobal.Divisibility.ColPins
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def lamOfCol {T : TiedDataSK ex} {P : RowSideFamily ex} (K : SquareIntegrableColumnsCompatible T P) :
    ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i) :=
  fun u i τ =>
    cast (congrArg (fun R : Ranks => DomWeight (R.N i)) K.kerTie.2.1)
      (K.c.W.lamTrue (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u)) i
        (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ)))

open Classical in

def psiCol {T : TiedDataSK ex} {P : RowSideFamily ex} (K : SquareIntegrableColumnsCompatible T P) : ∀ PP : Pl K.X.E, AddChar (kP PP) D.what₂.LL :=
  fun PP => if h : PP ∈ K.c.Pr.vGs then K.c.Ch.psi0 ⟨PP, h⟩ else 1

def nfMat {E : Type} [Field E] (n c : ℕ) (q : E) (nn : Fin c → ℤ) (z : Fin n → E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  fun a b =>
    if hb : b.1 < n then (if a = b then 1 else 0)
    else if hab : a = b then q ^ nn ⟨b.1 - n, by have := b.isLt; omega⟩
    else if h : b.1 = n ∧ a.1 < n then q ^ nn ⟨0, by have := b.isLt; omega⟩ * z ⟨a.1, h.2⟩ else 0

open Classical in

structure ColPins {T : TiedDataSK ex} {P : RowSideFamily ex} (K : SquareIntegrableColumnsCompatible T P) : Prop where

  grpTie : HEq P.grp (inferInstance : Group (Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r))

  psTie : HEq P.Ps K.c.Lv.grp ∧ HEq P.ψs K.c.Lv.chr

  pointCharacterEq : HEq P.P0 (P0 K.c.Pr.vGs K.c.Rk.r (psiCol K)).H ∧ HEq P.ψ0 (P0 K.c.Pr.vGs K.c.Rk.r (psiCol K)).chi

  wOk : K.c.W.Ok

  chOk : K.c.Ch.Ok

  hcTie : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    HEq (K.c.W.hc (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u))
      (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ))) (D.hcW u τ)

  wtTie : ∃ (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    Formalism.L2.Ker.KerEntTied.WtTie T.ker (lamOfCol K) sh n

  xgTie : ∀ χ : Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r → D.what₂.LL,
    χ ∈ K.c.Xg ↔ (fun g => χ (cast K.gEq (P.I.eG.symm g))) ∈ Formalism.L2.Col.XgE K.c.Am.σ₀ D.ntypes.e0

  qNF : ∀ (t : P.A3.fam3.base3.Tup) (j : ℕ) (b : (K.c.Li t).β j)
      (v : ↥(Formalism.L2.Col.uSG K.c.Pr.vGs (Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL)))),
      v.1 ∉ K.c.Pr.vGs → 1 ≤ j → j + 2 ≤ K.c.Rk.m →
      ∃ (nn : Fin (Formalism.L2.Col.cOf K.c.Rk j) → ℤ) (z : Fin (K.c.Rk.N j) → K.X.E),
        (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
        (fun l : Fin (K.c.Rk.N j + Formalism.L2.Col.cOf K.c.Rk j) => if h : l.1 < K.c.Rk.N j then z ⟨l.1, h⟩ else 0) ∈
          Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1 ∧
        (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
                  (((K.c.Li t).h j b v).toLinearMap.restrictScalars (𝓞 K.X.E)) =
          (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
            ((Matrix.toLin' (nfMat (K.c.Rk.N j) (Formalism.L2.Col.cOf K.c.Rk j) ((Formalism.L2.Col.qOf v.1 : ℕ) : K.X.E) nn z)).restrictScalars
              (𝓞 K.X.E))

  columnEvaluationOk : ∃ hM : (Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).Ok, ∀ u : D.what₂.Word,
    ∃ ι : (D.mem u).P.Mt ≃ₗ[ℂ] (Fin ((Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).hDim hM) → ℂ),
      (∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (y : Fin (rDim D P.A3.A P.Ps P.ψs t) → D.what₂.LL),
        ∃ (F' : (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun)
          (hm : F'.1 ∈ (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun),
          HEq ((Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).res
              (Formalism.L2.Col.mtildeKOk K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.hX) F')
            ((P.A3.A.fam.R t).S.basis.equivFun.symm
              (((P.A3.A.fam.R t).S.cutE (P.A3.A.fam.R t).r (lvlIdem (P.A3.A.fam.lvl P.Ps P.ψs).P
                (P.A3.A.fam.lvl P.Ps P.ψs).ψ)).mulVec y)) ∧
          ι ((D.eMt u).symm (ht ▸ P.I.jA t y)) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
        ∃ hm : ((K.c.ev P.Zs t F : Formalism.L2.Col.V0X K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Xg K.c.Lv) :
            (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun).1 ∈
            (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun,
          ι ((D.eMt u).symm (ht ▸ P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨_, hm⟩

end Formalism.L2.DIV

end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEightAlt
section
noncomputable section

open Module NumberField IsDedekindDomain

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section Arith

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure ArithAt (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A3.fam3.base3.J Pl) (bd : Fin m → ℝ) (dg : ℕ) : Prop where
  eig6 : ∑ j, R.hX j ≤ ∑ j, ((Zsc Pk.Zs).num C CH).l6 j
  hG0 : Real.log (Fintype.card G) ≤ R.lam0
  l3 : ∃ El3 : ℝ, ∑ j, ((Zsc Pk.Zs).num C CH).l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3 ∧
    El3 + lgDef R s + (∑ j, (((Zsc Pk.Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤ R.errB
  q : ∃ Q : ℝ, 0 ≤ ((Zsc Pk.Zs).num C CH).de ∧ 3 * ((Zsc Pk.Zs).num C CH).de * Q ≤ 1 ∧ 1 ≤ Q ∧
    boundBR Pk.core (lgDef R s) 1 (etaSumBound bd dg s) + ((Zsc Pk.Zs).num C CH).hh + 28 * ((Zsc Pk.Zs).num C CH).la ≤ Q
  la_le : ((Zsc Pk.Zs).num C CH).la ≤ R.lam0
  constant_ge_twenty_eight : 28 ≤ R.C0

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {cf : ConvFace A3.fam3.base3} {C CH : ℝ}
  {Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A3.fam3.base3.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} {bd : Fin m → ℝ}

def DivisionInputsWithoutNorm.ofRows (hNu : Submodule.IsLattice K Nu) (hsg : (Function.support (shiftZ sg)).Finite)
    (hXc : ∀ v, IsUnit ((Dc Pk.Zs).Xc u v).det) (ha : 0 < (Dc Pk.Zs).a u)
    (X0 : InfinitePlace K → Matrix (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0))
      (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧
      ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((A3.side3 P1 ψ1 Pk.Zs).HV A3.fam3.base3.μ0).map v.embedding)
    (ch : ColChain (Dc Pk.Zs) u) (hn : HtNums R (InfinitePlace K))
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤
        Real.exp hn.hPn)
    (cb : CBData ch.X ch.Kj) (nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v)
    (h11 : LiftExponentAtTwisted A3.A P0 ψ0 (A3.fam3.toSub2 Pk.Zs) Pk.core.base.μ Pk.core.base.Tw (Zsc Pk.Zs).J0)
    (dg : ℕ) (hdg : 0 < dg) (hdvd : ∀ j t, (A3.A.fam.L j t).DG (A3.A.fam.lvlA P0 ψ0) ∣ dg)
    (hA : ArithAt A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk R bd dg) :
    DivisionInputsWithoutNorm A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk R u Nu sg bd where
  Nu_lat := hNu
  sg_fin := hsg
  Xc_unit := hXc
  a_pos := ha
  X0 := X0
  base_matrix_det_unit := hX0
  ch := ch
  hn := hn
  nP := nP
  cb := cb
  nKcb := nKcb
  eig6 := hA.eig6
  h11 := h11
  dg := dg
  dg_pos := hdg
  dg_dvd := hdvd
  hG0 := hA.hG0
  El3 := Classical.choose hA.l3
  L3main := (Classical.choose_spec hA.l3).1
  errB := (Classical.choose_spec hA.l3).2
  Q := Classical.choose hA.q
  de0 := (Classical.choose_spec hA.q).1
  deQ := (Classical.choose_spec hA.q).2.1
  Q1 := (Classical.choose_spec hA.q).2.2.1
  Qb := (Classical.choose_spec hA.q).2.2.2
  la_le := hA.la_le
  constant_ge_twenty_eight := hA.constant_ge_twenty_eight

end Arith

end Formalism.L2.DIV

end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.SumLeEtaSumNum
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section N

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem lw_eq_lwP (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y) := by
  unfold SizeData₂.lwP
  rw [Equiv.apply_symm_apply]
  rfl

theorem ramw_eq_ramIdx (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ) := by
  rw [D.ram_eq, Equiv.apply_symm_apply, ← lf_eW_eq_ramw]
  rfl

theorem sum_le_etaSum_num (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (hnum : NumTie D A S0 tup)
    (hTw : TieTwRec L S0.Tw) (i : Fin m) :
    ∑ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) ≤ Formalism.MainNotions.etaSum L ((i : ℕ) + 1) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : D.what₂.places.Pl → ℝ,
      g = fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ ((i : ℕ) + 1) w : ℝ) := ⟨_, rfl⟩
  have hterm : ∀ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) = g (D.plEq.symm y) := by
    intro y hy
    have h1 : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y) := lw_eq_lwP D y
    have h2 : ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ) := ramw_eq_ramIdx D y
    have h3 : D.what₂.etaJ ((i : ℕ) + 1) (D.plEq.symm y) = A.fam.etaJ P0 ψ0 Zs i (S0.μ y) y := by
      rw [hnum.etaJ i (D.plEq.symm y), Equiv.apply_symm_apply, if_pos hy]
    rw [hg]
    dsimp only
    rw [← A.fam.etaJ_ramw P0 ψ0 Zs i (S0.μ y) y, h1, h2, h3]
    ring
  have hsi : ∑ w ∈ S0.Tw.image D.plEq.symm, g w = ∑ y ∈ S0.Tw, g (D.plEq.symm y) :=
    Finset.sum_image (fun x _ y _ hxy => D.plEq.symm.injective hxy)
  have hE : Formalism.MainNotions.etaSum L ((i : ℕ) + 1) = ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0), g w := by
    rw [hg]
    unfold Formalism.MainNotions.etaSum
    rfl
  rw [Finset.sum_congr rfl hterm, ← hsi, hE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    exact Finset.mem_filter.2 (hTw y hy)
  · intro w _ _
    rw [hg]
    exact mul_nonneg (mul_nonneg (zero_le_logWeight w) (Nat.cast_nonneg _)) (by exact_mod_cast D.what₂.etaJ_nonneg _ w)

theorem inEta_num (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (Ce : ℝ)
    (hN : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce) (hm : m = D.R.m) (hnum : NumTie D A S0 tup)
    (hTw : TieTwRec L S0.Tw) (hD : D.what₂.D0 = (A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0)) :
    InEta A.fam P0 ψ0 Zs S0.μ S0.Tw (fun _ => divSize L Ce) := by
  intro i
  have h1 := sum_le_etaSum_num L A hnum hTw i
  have hi : (i : ℕ) + 1 ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    exact Finset.mem_Icc.2 ⟨by omega, by have := i.isLt; omega⟩
  have h2 := hN ((i : ℕ) + 1) hi
  unfold Formalism.MainNotions.DIVinN_at at h2
  rw [hD] at h2
  unfold divSize
  exact h1.trans (h2.trans_eq (mul_comm _ _))

variable {I0 Ty : Type}

theorem inEta3_num (L : SizeData₂ D) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A3.fam3.amb3} {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (Ce : ℝ)
    (hN : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce) (hm : m = D.R.m)
    (hnum : NumTie D A3.A (A3.indefDown S0) tup) (hTw : TieTwRec L S0.Tw)
    (hD : D.what₂.D0 = (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P0 ψ0) (Zs.Z A3.A.fam.μ0)) :
    InEta A3.A.fam P0 ψ0 (A3.fam3.toSub2 Zs) S0.μ S0.Tw (fun _ => divSize L Ce) :=
  inEta_num L A3.A (Zs := A3.fam3.toSub2 Zs) (S0 := A3.indefDown S0) Ce hN hm hnum hTw hD

end N

end Formalism.L2.DIV

end
end


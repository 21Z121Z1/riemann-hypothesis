import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTieSat
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ContentZeroAtSmallPrimes
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.DropLevelBounds.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import Formalism.LocalToGlobal.CharacterGerms.Bundle0008
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7}

def plOf (D : D7) (z : RPl D.R) : D.what₂.Tau :=
  D.eTau.symm (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩)

def numOf (D : D7) (L : SizeData₂ D) : NumDatum where
  R := D.R
  sc := L.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊(D.s.Del : ℝ)⌋₊
  h0 := ⌊LevelStarExponents.h0 L⌋₊
  hc := fun z => D.hc (plOf D z)

def vdOf (D : D7) (p : ℕ) : ℝ := if p ∈ D.host.small then (padicValNat p D.host.QS : ℝ) else 1 / 2

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem TO_pos (Tp : ParamsT D L Pm) : 0 < Tp.TO := lt_of_lt_of_le (by omega) Tp.TO_40

def depOf (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) : DepData D.host.E :=
  depRun T EX ⟨Tp.TO, TO_pos Tp⟩ (vdOf D) (lR Tp hK) (fR Tp hK) (kaR Tp hK)

structure RunTie (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (ι : Bs.J → ℕ) : Prop where
  inR : ∀ j, InR D (ι j)
  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a
  conj : ∀ a : 𝓞 D.host.E, star (algebraMap (𝓞 D.host.E) K a) = algebraMap (𝓞 D.host.E) K (T.Q.H.bar a)
  E_eq : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) (depOf T EX Tp hK) v (ι j)
  σ_eq : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
  nn_eq : ∀ j, O.nnK j = nnKAt (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
  T_eq : O.T = (Tp.TO : ℝ)
  jets_eq_fact : O.g1 = D.host.g 0
  g2_eq : O.g2 = D.host.g 1
  cmQuadraticForm_eq_alternatingForm : O.q1 = D.host.q
  dd_eq : O.dd = D.host.d
  sm_eq : O.sm = D.host.small
  k_eq : O.k = (D.R.k : ℝ)
  m_eq : O.m = (D.R.m : ℝ)
  f_eq : O.f = (D.R.f : ℝ)
  x_eq : O.x = L.sc.x
  eps_eq : O.eps = L.sc.eps
  Sc_eq : O.Sc = L.Sc
  eta_eq : O.eta = L.etaSz
  bp_eq : O.bp = L.sc.b'
  depthNumbers_threshold_eq : O.X2 = L.sc.X'' D.R.n
  vd_eq : O.vd = vd2 D
  wt_eq : ∀ j, O.wt j = 2 * (D.R.f : ℝ) * L.sc.b
  th_eq : ∀ l, O.th l = Formalism.UnitaryBoundIntegral.thl D.R.k l
  ad_eq : ∀ l, O.ad l = 0
  DF_ge : ∀ j, (WeightAlgebra.DF (lR Tp hK (ι j)) : ℝ) ≤ O.DF

end GlobalTheory.RunDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.ExistsGeneratesIffFg
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlusRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev NormDatum (B : WeightFamilies.Prov D) := GlobalTheory.RunIn.SecNorm B

def NormDatum.sup (B : WeightFamilies.Prov D) : NormDatum B := GlobalTheory.RunIn.SecNorm.sup B
namespace NormDatum
variable (n : NormDatum B)

abbrev B' : WeightFamilies.Prov D := GlobalTheory.RunIn.SecNorm.base n

abbrev X' (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D n.B' P j := xplusN n.N n.h0 n.h1 n.h2 n.h3 n.h4 X E hM

abbrev S' (S : Scal B) : Scal n.B' := scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S

abbrev G' {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) :
    GlobalFamilyData (n.X' X E hM) ka wL wF := gd2XplusN n.N n.h0 n.h1 n.h2 n.h3 n.h4 G E hM

end NormDatum

def Generates (X : PJ D B P j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) {n : ℕ} (gens : Fin n → B.Cusp j w) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range gens) = X.WWc s w

example (B : WeightFamilies.Prov D) :
    NormDatum.B' (B := B) ⟨B.l2NormAlt, B.l2Norm_nonneg_bis, B.l2Norm_eq_zero_iff, B.l2Norm_smul_alt, B.l2Norm_add_le', B.l2Norm_le_supNorm_alt⟩ = B := rfl

example (B : WeightFamilies.Prov D) : (NormDatum.sup B).B'.l2NormAlt = (NormDatum.sup B).B'.supN := rfl
end GlobalTheory.PlusRec
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace GlobalTheory.RowAt

open NumberField Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV GlobalTheory.RowLaw
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def gap (r : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  if 1 ≤ k ∧ k ≤ r then a (k - 1) - (if k < r then a k else 0) else 0

section Supply

variable {C : Type} [Field C]

def Supply (V : VF C) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (Z : Finset Orb) (n m : ℕ)
    (big : Orb → Fin 2 → ZMod d → Prop) (rk : Orb → Fin 2 → ZMod d → ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
    (nW : ℕ) (ν : ℝ) : Prop :=
  ∃ (I J : Orb → Fin 2 → Type) (_ : ∀ o g, Fintype (I o g)) (_ : ∀ o g, Fintype (J o g))
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, RF.Flag (X o)),
    (∀ o, (X o).n = n ∧ (X o).m = m) ∧ (∀ o ∈ Z, ∀ g s, ((X o).big g s ↔ big o g s) ∧ (X o).rkF g s = rk o g s) ∧
      RF.ValBlocks X F Z nW ga ν

def SupplyC (V : VF C) (Orb : Type) [Fintype Orb] (n m : ℕ) (rk : Orb → ZMod 2 → ℕ) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (nW : ℕ) (ν : ℝ) : Prop :=
  ∃ (I J : Orb → Fin 2 → Type) (_ : ∀ o g, Fintype (I o g)) (_ : ∀ o g, Fintype (J o g))
    (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, RF.Flag (X o)),
    (∀ o, (X o).n = n ∧ (X o).m = m ∧ (X o).Alt ∧ ∀ s, (X o).rkF 0 s = rk o s) ∧ RF.ValBlocksC X F nW gaC ν

end Supply

section ND

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def c2 (X : RawChart C d I κ) (u : κ → C) : MvPowerSeries (Fin 2 × κ) C :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × κ => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1)
    (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1) + hAt X (gp C κ 0) (gp C κ 2) -
      hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2)))

def cob (X : RawChart C d I κ) (b : MvPowerSeries κ C) : MvPowerSeries (Fin 2 × κ) C :=
  MvPowerSeries.subst (addP X (gp C κ (0 : Fin 2)) (gp C κ 1)) b - MvPowerSeries.subst (gp C κ (0 : Fin 2)) b -
    MvPowerSeries.subst (gp C κ (1 : Fin 2)) b

def NonDeg (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ γ : κ → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (addP X (fun j => cvAt (MvPowerSeries.X 0) (γ j)) (fun j => cvAt (MvPowerSeries.X 1) (γ j)) i -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : MvPowerSeries κ C, IntS V b ∧
      ∀ μ, V.MM (MvPowerSeries.coeff μ (c2 X (fun i => PowerSeries.coeff 1 (γ i)) - cob X b))

def hCoef (X : RawChart C d I κ) (γ : κ → PowerSeries C) (n : ℕ) : MvPowerSeries κ C :=
  fun μ => PowerSeries.coeff n (alongCv γ (fun ν : κ →₀ ℕ => MvPowerSeries.coeff
    (ν.mapDomain (fun x : κ => ((0 : Fin 2), x)) + μ.mapDomain (fun x : κ => ((1 : Fin 2), x))) X.h))

end ND

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure LabS (E : Type) [Field E] (Orb : Type) where
  tau : Orb → ZMod 2 → (E →+* ℂ)
  n : ℕ
  j : ℕ
  j' : ℕ

abbrev LabS.II {Orb : Type} (lab : LabS E Orb) (Dw : Datum H) (o : Orb) : Type :=
  Σ s : ZMod 2, Fin (Dw.mult (lab.tau o s))

def LabS.RankOK {Orb : Type} (lab : LabS E Orb) (Dw : Datum H) : Prop :=
  ∀ o, Dw.mult (lab.tau o 0) = lab.n + lab.j ∧ Dw.mult (lab.tau o 1) = lab.j'

variable {Dw : Datum H} {lv : Level H} {Xo : Moduli Dw lv} {c : Coeff lv}
variable {C : Type} [Field C] [CharZero C]

def FrobOrd (V : VF C) {T : CDVR} (io : c.F →+* T.Fr) (ι : T.Fr →+* C) {d : ℕ} (tau : ZMod d → (E →+* ℂ)) : Prop :=
  ∀ s x, V.MM (emA3 io ι (tau (s + 1)) x - emA3 io ι (tau s) x ^ V.l)

structure ArithS (V : VF C) {T : CDVR} (io : c.F →+* T.Fr) (ι : T.Fr →+* C) {Orb : Type} (lab : LabS E Orb) : Prop where
  inj : Function.Injective fun x : Orb × ZMod 2 => lab.tau x.1 x.2
  conj : ∀ o s, lab.tau o (s + 1) = ComplexEmbedding.conjugate (lab.tau o s)
  frob : ∀ o, FrobOrd V io ι (lab.tau o)
  unr : ¬ (V.l : ℤ) ∣ NumberField.discr E

variable [StarRing (𝓞 E)] {V : VF C} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

structure IsSelfOf (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) {Orb : Type}
    (lab : LabS E Orb) (p : ∀ o, SelfData Y 2 (lab.II Dw o)) : Prop where
  em : ∀ o s, (p o).em s = emA3 io ι (lab.tau o s)
  hd : ∀ o, (p o).hd = 1
  e : ∀ o x i, (p o).e x i = ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)
  ty0 : ∀ o x, (p o).ty0 x = x.1
  n : ∀ o, (p o).n = lab.n
  j : ∀ o, (p o).j = lab.j
  j' : ∀ o, (p o).j' = lab.j'
  big : ∀ o g s, (p o).big g s ↔ s = ((g.val : ℕ) : ZMod 2)

section Img

variable {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type}
  [∀ o, Fintype (I0 o)]

def imgFamS (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (Ls : LetSys C dd) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) :
    Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

end Img

def tauIn (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (l : ℕ) (z : RPl N.R) (g : Fin 2) (s : ZMod (N.ordP l)) : E →+* ℂ :=
  if g = RF.bg s then pl (N.pos l z s.val) else ComplexEmbedding.conjugate (pl (N.pos l z s.val))

def tauSp (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) {d : ℕ} (pos : RPl N.R → ℕ → RPl N.R) (z : RPl N.R) (g : Fin 2)
    (s : ZMod d) : E →+* ℂ :=
  if g = 0 then pl (pos z s.val) else ComplexEmbedding.conjugate (pl (pos z s.val))

def tauC (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (z : RPl N.R) (s : ZMod 2) : E →+* ℂ :=
  if s = 0 then pl z else ComplexEmbedding.conjugate (pl z)

end GlobalTheory.RowAt
end
end


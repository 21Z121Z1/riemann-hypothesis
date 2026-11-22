import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AmpleVanishingSym
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IffAmpleVanishing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sizes

variable {D : D7}

abbrev PlL (D : D7) : Type := HeightOneSpectrum (𝓞 D.what₂.LL)

def Loss (dl : PlL D → ℝ) (B : ℝ) : Prop :=
  (∀ w, 0 ≤ dl w) ∧ {w | dl w ≠ 0}.Finite ∧ ∀ s : Finset (PlL D), ∑ w ∈ s, lw w * dl w ≤ B

def LossLe (w : PlL D) (z : ℂ) (a : ℝ) : Prop := ∃ y, D.what₂.embLL y = z ∧ (y = 0 ∨ -a ≤ (vw w y : ℝ))

def AbsLe (σ : D.what₂.LL →+* ℂ) (z : ℂ) (B : ℝ) : Prop := ∃ y, D.what₂.embLL y = z ∧ ‖σ y‖ ≤ Real.exp B

variable {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n')

def InLat (w : PlL D) (a : ℝ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (v : VV ℂ lam) : Prop :=
  ∃ (u : VV D.what₂.LL lam) (s : D.what₂.LL), GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u = v ∧ s ≠ 0 ∧ (vw w s : ℝ) ≤ a ∧
    s • u ∈ nabAtr (labLL D) lam Λ

def nrm (H : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (v : VV ℂ lam) : ℝ := (pairK lam H v v).re

def NrmLe (σ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) : Prop :=
  ∃ u : VV D.what₂.LL lam, GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u = v ∧ nrm lam (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ lam u) ≤ B

theorem LossLe.mono {w : PlL D} {z : ℂ} {a a' : ℝ} (h : LossLe w z a) (ha : a ≤ a') : LossLe w z a' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.imp_right fun h => (neg_le_neg ha).trans h⟩

example (w : PlL D) (σ : D.what₂.LL →+* ℂ) : LossLe w 0 0 ∧ AbsLe σ 1 0 := ⟨⟨0, map_zero _, Or.inl rfl⟩, 1, map_one _, by simp⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def sig : ℝ := ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal)

def bOne (C b : ℝ) : ℝ := C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log b + sig G) * b

def aOne (C b : ℝ) : ℝ := C * D.R.f * bigN D * b * Real.log b + C * D.R.m * (bigN D : ℝ) ^ 2 * sig G

def Away (t : T) (w : PlL D) : Prop :=
  ∀ PP ∈ L.Q t, PP.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∀ l : ℕ, l.Prime → (l : 𝓞 D.host.E) ∈ PP.asIdeal → (l : 𝓞 D.what₂.LL) ∉ w.asIdeal

open Classical in

def depL (l : ℕ) : ℕ := (G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).sup (depthAt G)

variable {G} {W : G.Weil} (S : GridChoice W Set.univ)

def latAt (X : Node) (x : FinPt G X) : Submodule (𝓞 D.host.E) (Fin (G.V X).rank → D.host.E) :=
  (Formalism.UG.CS.globLat (finG (G.V X) x) (G.Λ X)).comap ((S.N.fr X).1.mulVecLin.restrictScalars (𝓞 D.host.E))

def Occurs (t : T) (Φ : G.Datum) (β : CosFam G t) (d : PureDat G t) : Prop :=
  β ∈ S.supp t Φ ∧ ∃ τ, IsCosetExpansion S t Φ β (expDepth S t Φ β) τ ∧ d ∈ τ.support

def topVal (Ψ : GLf G → WtSp G) (x : FinPt G (.top 0)) : VV ℂ (wt G (.top 0)) :=
  rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (psiC Ψ x)

def rowVal (v : VV ℂ (listedWt G (.grid 0 D.R.m))) : VV ℂ (wt G (.grid 0 D.R.m)) :=
  rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) v)

variable (G) in

abbrev lastPair : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) →ₗ[ℂ] ℂ :=
  brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))

end Sizes

abbrev ChQ := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}, Face D A → Choice R → ℝ → ℝ → Prop

def BigC (Q : ChQ) : Prop :=
  ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → Q F ch C large₂.sc.b

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ)

def formOf (t : T) (x : Fin ((A.fam.R t).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL) : A.fam.amb.FR t :=
  (A.fam.R t).S.basis.equivFun.symm (((A.fam.R t).vE (A.fam.lvl F.P0 F.ψ0)).mulVec x)

def DepthAt : Prop := ∀ t Φ, ∀ β ∈ ch.S.supp t Φ,
  (∃ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ) ∧
    ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      padicValNat l (expDepth ch.S.toGridChoice t Φ β) ≤ depL ch.G l

def FinScalAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ w : PlL D, LossLe w ch.S.sAA (dl w)

def FinCoefAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ, ∀ β ∈ ch.S.supp t Φ,
  LossLe w (∏ v, ((ch.S.term t Φ β v).coef : ℂ)) (dl w)

def FinDatAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ, ∀ β ∈ ch.S.supp t Φ, ∀ x y,
  LossLe w (∏ v, (ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y)) (dl w)

def FinGamAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ t (w : PlL D) Φ β (c : ch.S.Classes t Φ β),
  LossLe w (ch.S.invGam c) (dl w)

def FinTopAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ β d, Occurs ch.S.toGridChoice t Φ β d →
  ∀ (c : ch.S.Classes t Φ β) (j : Fin D.R.m) (a : ℝ) v, InLat _ w a (latAt ch.S.toGridChoice (.top j) (ch.S.ptTop c j)) v →
    InLat _ w (a + dl w) (latAt ch.S.toGridChoice (.top (j + 1)) (ch.S.ptTop c (j + 1)))
      (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v)

def FinRowAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ β d, Occurs ch.S.toGridChoice t Φ β d →
  ∀ (c : ch.S.Classes t Φ β) (i : Fin D.R.m) (a : ℝ) v,
    InLat _ w a (latAt ch.S.toGridChoice (.grid i D.R.m) (ch.S.ptRow c i)) v →
    InLat _ w (a + dl w) (latAt ch.S.toGridChoice (.grid (i + 1) D.R.m) (ch.S.ptRow c (i + 1)))
      (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v)

def FinPairAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ (w : PlL D) (y : FinPt ch.G (.grid D.R.m D.R.m)) (a a' : ℝ) u v,
  InLat _ w a (latAt ch.S.toGridChoice (.top D.R.m) (finEmb ch.G.sp.topDec y)) u →
    InLat _ w a' (latAt ch.S.toGridChoice (.grid D.R.m D.R.m) y) v → LossLe w (lastPair ch.G u v) (a + a' + dl w)

def FinPsiAt : Prop := ∀ (w : PlL D) c, ∀ u ∈ wLat ch.G (ch.rp.lat c), ∀ x,
  InLat _ w 0 (latAt ch.S.toGridChoice (.top 0) x) (topVal ch.S.toGridChoice (ch.rp.delta c u) x)

def FinFormAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ t (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w (dl w) (latAt ch.S.toGridChoice (.grid 0 D.R.m) y)
    (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y))

def FinAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b / 2) ∧ ∀ X' M, IsTestLat ch.G ch.rp ch.n ch.e X' M →
  ∀ t w, Away ch.G t w → ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y : Fin ch.n → D.what₂.LL,
    (∀ a, D.what₂.embLL (y a) = vK ch t (formOf F t x) a) → ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ dl w ∧ s • y ∈ M

def AwayAt : Prop := ∀ w, Away ch.G (R.mu w) w

def InfScalAt : Prop := ∀ σ : D.what₂.LL →+* ℂ, AbsLe σ ch.S.sAA (D.R.m * aOne ch.G C b)

def InfTensAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ x y,
  AbsLe σ ((∏ v, ((ch.S.term A.μ0 Φ β v).coef : ℂ)) *
    ∏ v, (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G)

def InfCountAt : Prop := (Nat.card ch.G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) ∧ ∀ Φ,
  ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) ∧ ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ τ,
    IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ →
      (τ.support.card : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def InfClassAt : Prop := (Nat.card ch.G.ClPlus : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) ∧ ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ,
  (Nat.card (ch.S.Classes A.μ0 Φ β) : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def InfTopAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m) B v,
    NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B)

def InfRowAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m) B v,
    NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v) (Real.exp (g p) * B)

def InfPairAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) B B' u v, NrmLe _ σ u B → NrmLe _ σ v B' →
  ∃ y, D.what₂.embLL y = lastPair ch.G u v ∧ ‖σ y‖ ^ 2 ≤ Real.exp (aOne ch.G C b) * B * B'

def InfPsiAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) c u x, NrmLe _ σ (topVal ch.S.toGridChoice (ch.rp.delta c u) x)
  (nrm (LaP ch.G) (fun τ => (gramKd (emb D) (Xp ch.G).gram τ).map σ) (GlobalTheory.CoefModel.mapVV σ _ u))

def InfFormAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) x y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    (Real.exp (D.R.m * aOne ch.G C b) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re)

def InfAt : Prop := ∀ X' M, IsTestLat ch.G ch.rp ch.n ch.e X' M → ∀ X, IsMetric ((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)) X →
  ∀ V : Matrix (Fin ch.n) (Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0))) D.what₂.LL,
    (∀ x a, D.what₂.embLL (V.mulVec x a) = vK ch A.μ0 (formOf F A.μ0 x) a) →
      Formalism.HN.htMap (Pi.basisFun _ _) X (Pi.basisFun _ _) X' V.mulVecLin ≤ D.R.m * aOne ch.G C b

end Claims

def DepthK : Prop := BigC fun _ ch _ _ => DepthAt ch

def FinScalK : Prop := BigC fun _ ch C b => FinScalAt ch C b

def FinCoefK : Prop := BigC fun _ ch C b => FinCoefAt ch C b

def FinDatK : Prop := BigC fun _ ch C b => FinDatAt ch C b

def FinGamK : Prop := BigC fun _ ch C b => FinGamAt ch C b

def FinTopK : Prop := BigC fun _ ch C b => FinTopAt ch C b

def FinRowK : Prop := BigC fun _ ch C b => FinRowAt ch C b

def FinPairK : Prop := BigC fun _ ch C b => FinPairAt ch C b

def FinPsiK : Prop := BigC fun _ ch _ _ => FinPsiAt ch

def FinFormK : Prop := BigC fun F ch C b => FinFormAt F ch C b

def FinK : Prop := BigC fun F ch C b => FinAt F ch C b

def AwayK : Prop := BigC fun _ ch _ _ => AwayAt ch

def InfScalK : Prop := BigC fun _ ch C b => InfScalAt ch C b

def InfTensK : Prop := BigC fun _ ch C _ => InfTensAt ch C

def InfCountK : Prop := BigC fun _ ch C b => InfCountAt ch C b

def InfClassK : Prop := BigC fun _ ch C b => InfClassAt ch C b

def InfTopK : Prop := BigC fun _ ch C b => InfTopAt ch C b

def InfRowK : Prop := BigC fun _ ch C b => InfRowAt ch C b

def InfPairK : Prop := BigC fun _ ch C b => InfPairAt ch C b

def InfPsiK : Prop := BigC fun _ ch _ _ => InfPsiAt ch

def InfFormK : Prop := BigC fun F ch C b => InfFormAt F ch C b

def InfK : Prop := BigC fun F ch C b => InfAt F ch C b

end GlobalTheory.SumSize

end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsRelAcyclicPolAVBase
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxForm (IsRelAcyclic)
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.RelAcyclicAmple
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleSymModel

theorem hyp_ell {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    IsAbelianScheme (WeierstrassCurve.ellPolAV W).A ∧ (WeierstrassCurve.ellPolAV W).g = 1 ∧
      (WeierstrassCurve.ellPolAV W).L.IsLB ∧
      Out.RelAmple (WeierstrassCurve.ellPolAV W).A (WeierstrassCurve.ellPolAV W).L ∧
      Out.Sym (WeierstrassCurve.ellPolAV W).A (WeierstrassCurve.ellPolAV W).L :=
  ⟨(WeierstrassCurve.ellPolAV W).isAb, WeierstrassCurve.ellPolAV_g W, (WeierstrassCurve.ellPolAV W).isLB,
    (WeierstrassCurve.ellPolAV W).ample, (WeierstrassCurve.ellPolAV W).sym⟩

theorem isElliptic_complex : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℂ).IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩

theorem isElliptic_char_two (K : Type) [Field K] [CharP K 2] :
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    have h : (27 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination 13 * h2
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [h]
    norm_num⟩

theorem isRelAcyclic_pw (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℤ) (hl : 1 ≤ l) :
    IsRelAcyclic P.A.hom P.A.hom (AbLaw.pw P.L l) := by
  intro U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    exact (cechComplex_exactAt_succ_iff_cube _ n).2
      (PolVanishing.exactAt_secCube_pw abelianSchemeLaws_all.1 K P l κ W hl hW hWU (n + 2))
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

theorem isRelAcyclic_polAV (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) :
    IsRelAcyclic P.A.hom P.A.hom P.L := by
  have h := isRelAcyclic_pw K P 1 le_rfl
  rwa [AbLaw.pw_one] at h

theorem isRelAcyclic_of_sym (AV : GlobalTheory.AmpleSym.AmpleVanishingSym) :
    ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] (p : S ⟶ Sp k) (A : Over S) [GrpObj A],
      IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → Out.Sym A L →
      IsRelAcyclic (A.hom ≫ p) A.hom L := by
  intro k _ S _ p A _ hA L hL hamp hsym U hU κ _ _ W hW hWU n
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let t : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  have h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨hproj, hsm, -, -⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp
    Γ(S, U) t _ _ _ h
  haveI : Flat (pullback.snd A.hom t) := inferInstance
  have hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U := by
    ext x
    change x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)
    rw [Scheme.Pullback.range_fst, hU.range_fromSpec]
    rfl
  have hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange := fun i =>
    hrange ▸ (le_iSup W i).trans hWU.le
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle
  refine HomologicalComplex.ExactAt.of_iso ?_ e
  refine (cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_
  refine cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _
    (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n
  · intro P hP
    letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P
    let χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P) :=
      (algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)
    refine ⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩
    · rw [RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]
    · intro κ' _ _ D' hD' hc' m
      have := hA.proper
      let B := (Over.pullback t).obj A
      have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj t A hA
      have : IsProper B.hom := hB.proper
      have hLB : (L.pull (pullback.fst A.hom t)).IsLB := LB.isLB_pull hL _
      have hampB : Out.RelAmple B (L.pull (pullback.fst A.hom t)) := AmpleBaseChange.relAmple_of_isPullback hL hamp h
      have hsB : Out.Sym B (L.pull (pullback.fst A.hom t)) :=
        PolBaseChange.sym_pull (isGrpPullback_pullback A t) hsym
      let A₀ := (Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj B
      have hA₀ : IsAbelianScheme A₀ := isAbelianScheme_pullback_obj _ B hB
      have hamp₀ := AmpleBaseChange.relAmple_of_isPullback hLB hampB
        (IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom χ)))
      have hs₀ := PolBaseChange.sym_pull (isGrpPullback_pullback B (Spec.map (CommRingCat.ofHom χ))) hsB
      exact AV _ A₀ hA₀ _ (LB.isLB_pull hLB _) hamp₀ hs₀ ⊤ (isAffineOpen_top _) κ' D' hD'
        (by rw [hc', Scheme.Hom.preimage_top]) m
  · rw [← Scheme.Hom.preimage_iSup, hWU, ← hrange]
    exact Scheme.Hom.preimage_opensRange _

def polPull {S : Scheme.{0}} (P : Out.PolAV S) {R : Type} [CommRing R] (f : Sp R ⟶ S) : Out.PolAV (Sp R) :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have := P.isAb.proper
  { A := (Over.pullback f).obj P.A
    isAb := isAbelianScheme_pullback_obj f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
    ktriv := by
      obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
      exact kTriv_pull h P.isLB hL' ((isGen_iff w).1 hw) P.ktriv }

theorem isRelAcyclic_polAV_base (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] (p : S ⟶ Sp k)
    (Q : Out.PolAV S) : IsRelAcyclic (Q.A.hom ≫ p) Q.A.hom Q.L := by
  intro U hU κ _ _ W hW hWU n
  let A := Q.A
  let L : LB A.left := Q.L
  have hA : IsAbelianScheme A := Q.isAb
  have hL : L.IsLB := Q.isLB
  have hamp : Out.RelAmple A L := Q.ample
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let t : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  have h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨hproj, hsm, -, -⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp
    Γ(S, U) t _ _ _ h
  haveI : Flat (pullback.snd A.hom t) := inferInstance
  have hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U := by
    ext x
    change x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)
    rw [Scheme.Pullback.range_fst, hU.range_fromSpec]
    rfl
  have hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange := fun i =>
    hrange ▸ (le_iSup W i).trans hWU.le
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle
  refine HomologicalComplex.ExactAt.of_iso ?_ e
  refine (cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_
  refine cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _
    (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n
  · intro P hP
    letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P
    let χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P) :=
      (algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)
    refine ⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩
    · rw [RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]
    · intro κ' _ _ D' hD' hc' m
      exact isRelAcyclic_polAV _ (polPull (polPull Q t) (Spec.map (CommRingCat.ofHom χ))) ⊤ (isAffineOpen_top _) κ' D' hD'
        (hc'.trans (Scheme.Hom.preimage_top _).symm) m
  · rw [← Scheme.Hom.preimage_iSup, hWU, ← hrange]
    exact Scheme.Hom.preimage_opensRange _

end GlobalTheory.AmpleSymModel
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointShiftStOfPlaceShiftSt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.PlaceShiftModel

open NumberField IsDedekindDomain GlobalTheory.CompHt GlobalTheory.HTLat

theorem det_ne_zero {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {n : ℕ} {La : Submodule O U} {b : Fin n → U} {g : Matrix (Fin n) (Fin n) C}
    (h : IsLatBasis C La fun i => ∑ j, g i j • b j) : g.det ≠ 0 := by
  have hl : LinearIndependent C g.row :=
    LinearIndependent.of_comp (Fintype.linearCombination C b) h.1
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)).ne_zero

variable {E : Type} [Field E] [NumberField E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem norm_le_one (τ : E →+* ℂ_[ℓ]) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  rw [← algebraMap_embO (PadicComplexInt.integers ℓ) τ a]
  exact (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 (Subtype.prop _)

theorem norm_ell : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] ℂ_[ℓ]), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_place (τ : E →+* ℂ_[ℓ]) :
    ∃ w : HeightOneSpectrum (𝓞 E), ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ (a : E)‖ < 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        change ‖τ ((a + b : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        change ‖τ ((c * a : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one τ c) (norm_nonneg _) ha }
  refine ⟨⟨I, ⟨fun h => ?_, fun {a b} h => ?_⟩, fun h => ?_⟩, fun _ => Iff.rfl⟩
  · have : ‖τ ((1 : 𝓞 E) : E)‖ < 1 := (Ideal.eq_top_iff_one I).1 h
    simp at this
  · by_contra hn
    rw [not_or] at hn
    have ha : ‖τ (a : E)‖ = 1 := le_antisymm (norm_le_one τ a) (not_lt.1 hn.1)
    have hb : ‖τ (b : E)‖ = 1 := le_antisymm (norm_le_one τ b) (not_lt.1 hn.2)
    have h' : ‖τ ((a * b : 𝓞 E) : E)‖ < 1 := h
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at h'
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb
    rw [ha, hb] at h'
    simp at h'
  · have : (ℓ : 𝓞 E) ∈ I := by
      change ‖τ ((ℓ : 𝓞 E) : E)‖ < 1
      rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
      exact norm_ell
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast this)

theorem exists_place_emb (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (w : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ_[ℓ]), ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ (a : E)‖ < 1 := by
  have : Nonempty (E →+* ℂ_[ℓ]) := Fintype.card_pos_iff.1 (by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
  obtain ⟨τ⟩ := this
  obtain ⟨w, hw⟩ := exists_place τ
  exact ⟨w, τ, hw⟩

theorem pointShiftSt_of_placeShiftSt (h : PlaceShiftSt) : PointShiftSt := by
  intro E _ _ _ H hH ℓ _ τ
  obtain ⟨w, hw⟩ := exists_place τ
  obtain ⟨κ₁, κ₂, hκ⟩ := h E H hH ℓ w
  exact ⟨κ₁, κ₂, hκ τ hw⟩

end GlobalTheory.FlatCM.PlaceShiftModel

end
end


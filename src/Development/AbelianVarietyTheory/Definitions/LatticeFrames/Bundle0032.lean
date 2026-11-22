import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def LevTrace : Prop :=
  ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔
      (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ rJ W) ∧
    ∀ hy : (y : GL _ _) ∈ (F0 W u).cls0.lev.U, (((F0 W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      rChi W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1

structure BotTie {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) : Prop where
  lev : ∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, B.lev = f.c.B 0 D.R.rS h₀
  adapted : B.Adapted (W.S.tr u).wt
  norm : ∃ μ lam : D.host.E, μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
    (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
    ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (f.c.bes j 0 h).ζ
  last : ∀ i, (G i).z₀ = fun r => (ofSplit (G i).q).pr (o.ζ₀ r)
  lat : ∀ p, p ∉ v.tP → GlobalTheory.FinPl.latV (D.sp.X 0) (f.g.x 0).L (· = p) = GlobalTheory.FinPl.latV (D.sp.X 0)
    ((F0 W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
      (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = p)
  trace : LevTrace f B

def ChartZero : Prop :=
  ∀ t, ∃ α₀ : (f.t t).Ch 0, (∀ α, α = α₀) ∧ (f.t t).e 0 α₀ = Finsupp.single (f.g.b 0) 1 ∧
    (∀ φ, col0 f t φ ∈ (f.t t).Ram 0 ∧ ∀ y, (f.t t).rd 0 α₀ (col0 f t φ) y = (chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) ∧
    ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = col0 f t φ

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

structure LevAtZ (F : Formalism.L2.Forms.Forms0 D u) : Prop where
  lat : ∀ z : Fin (D.sp.X 0).rank → D.host.E,
    (z ∈ (a.x 0).L ∧ ∀ i, (o.β 0 i).b' *ᵥ (fun r => (o.p i).pr (incA D (z r))) ∈ (o.Q 0 i).ker) ↔
    (fun i => z (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)).symm i)) ∈ F.cls0.lev.Lb
  lev : ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ F.cls0.lev.U ↔ InLev0 o G κ) ∧
    ∀ (hy : (y : GL _ _) ∈ F.cls0.lev.U) (g : ∀ PP : a.c.Pg, GL (XIx (Fin D.R.k) (Fin D.R.t) 0) (G PP).k)
      (hg : ∀ PP, embX ((G PP).s + 1) (g PP) ∈ (G PP).lev0.J), (∀ PP, (G PP).MatAt κ (g PP)) →
      ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) * ∏ PP, (((G PP).lev0.lam ⟨_, hg PP⟩ : ℂˣ) : ℂ) = 1

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

def LevZ {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {v : B.Word}
    (a : XPart (I.rec7 l Z) v) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1) : Prop :=
  LevAtZ o G (w.C.forms v).to0 ∧ Arith o G

end World

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

def idV (𝔞 : FI D) (v : Pl D) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ w, w ≠ v → evalV D.host.F w α = 0) ∧ ∃ a ∈ 𝔞,
    y = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a}

def dI (D : D7) : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar

def cI (D : D7) (j : ℕ) : FI D :=
  FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (j / 2)) * (D.host.AA * D.host.AAbar⁻¹) ^ ((D.R.m - j) / 2)

def bI (D : D7) (j ρ i : ℕ) : FI D := dI D ^ (ρ - i) * cI D j

def MonoId {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) : Prop :=
  MonoAt d L L₀ v ∧ ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a ∈ idV (𝔟 i) v

def LineId {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a ∈ idV 𝔠 v

def LineLatAt (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (LL : Lat L) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV ζ ∈ latV L LL (· = v) ↔ a ∈ idV 𝔠 v

variable {a : XPart D u}

structure YPart.Sk (b : YPart a) (ζ₀ : Fin a.Lz.rank → D.host.E)
    (τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (b.bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E) : Prop where
  base : (a.dat b).Base
  chBF : ∀ j ρ h, (b.sBF j ρ h).χV = a.c.chS (j + 1) ∧ (b.sBF j ρ h).χW = a.c.chT (j + 1)
  chFB : ∀ j σ h, (b.sFB j σ h).χV = a.c.chS (j + 1 + 1) ∧ (b.sFB j σ h).χW = a.c.chT (j + 1 + 1)
  norm : ∀ j ρ h, (star (b.bes j ρ h).ζ ⬝ᵥ (b.bes j ρ h).L.gram *ᵥ (b.bes j ρ h).ζ) *
    (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)
  tau : ∀ j h, τ j h *ᵥ ζ₀ = D.host.xi0 ^ (D.R.m / 2) • (b.bes j 0 h).ζ

@[reducible] def YPart.withT (b : YPart a) (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V) : YPart a := { b with t := t }

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {o : OffX a k ι} {b : YPart a}

structure CoreLat (o : OffX a k ι) (b : YPart a)
    (β₀ : ∀ j ρ h i, Frame (o.p i) (b.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)) (M : ∀ j ρ h, Lat (b.bes j ρ h).V₀) : Prop where
  sd : ∀ j ρ h, IsSelfDualC _ (M j ρ h)
  glued : ∀ j ρ h i, GluedCore ((a.dat b).B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i)
  split : ∀ j ρ h, ∃ LL, IsSelfDualC (b.bes j ρ h).L LL ∧ ∀ v, ¬ o.atT v →
    LineLatAt _ (b.bes j ρ h).ζ (cI D j) LL v ∧ OrthAt (b.bes j ρ h).o (M j ρ h) (a.x j).L LL v
  line : ∀ j ρ h v, LineId (b.bes j ρ h).o (b.bes j ρ h).ζ (M j ρ h) (cI D j) v

structure BigLat (y : OffY o b) : Prop where
  core : CoreLat o b y.β₀ y.M
  moves : ∀ j, j < D.R.m → IsSelfDualC ((a.dat b).st j).V (y.L j) ∧
    ∀ P, Moves ((a.dat b).st j).V (b.t j) ((a.dat b).st j).Λ (y.L j) P
  even : ∀ j ρ h v, v ∉ a.c.S → MonoId (b.bes j ρ h).d (y.L j) (y.M j ρ h) (bI D j ρ) v
  odd : ∀ j ρ h v, v ∉ a.c.S →
    MonoId (b.jac j ρ h).d (y.L (j + 1)) (a.x (j + 1)).L (fun i => D.host.AA⁻¹ * bI D j ρ i) v

open GlobalTheory.LocMod in

structure GY {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GX a ζ₀ PP) (b : YPart a)
    (τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (b.bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E) where
  FY : ∀ j c, j + c = G.s + 1 → GlobalTheory.LocMod.Frame G.k ((a.dat b).st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)
  sc : ℕ → G.k
  sc_unit : ∀ j, valuation G.k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit G.q).xi
  hz_unit : ∀ j ρ h, valuation G.k ((ofSplit G.q).hz ((a.dat b).B j ρ h)) = 1
  bes : ∀ j ρ h c (hc : j + c = G.s + 1),
    (ofSplit G.q).IsBesFrame ((a.dat b).B j ρ h) (sc j) (G.FX j (by omega)) (FY j c hc)
  jac : ∀ j ρ h c (hc : j + 1 + c = G.s + 1), (ofSplit G.q).IsJacFrame ((b.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit G.q).hz ((a.dat b).B j ρ h)) (G.FX (j + 1) (by omega)) (FY (j + 1) c hc)
  tau : ∀ h, (τ G.s h).map (ofSplit G.q).pr *ᵥ G.z₀ =
    (-((ofSplit G.q).xi * sc G.s)) • fun i => (ofSplit G.q).pr ((b.bes G.s 0 h).ζ i)

open GlobalTheory.LocMod in

def GY.Framed {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} {G : GX a ζ₀ PP} {τ} (H : GY G b τ)
    (t : ∀ j, GA D ((a.dat b).st j).V) : Prop :=
  ∀ j c (hc : j + c = G.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin ((a.dat b).st j).V.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit G.q) ((a.dat b).st j).V (t j) ((a.dat b).st j).β
      (((H.FY j c hc).β * ((G.S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i))

structure YGood (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1) (b : YPart a) (y : OffY o b)
    (H : ∀ PP, GY (G PP) b y.τ) : Prop where
  sk : b.Sk o.ζ₀ y.τ
  lat : BigLat y
  framed : ∀ PP, (H PP).Framed b.t

theorem cI_step (D : D7) {j : ℕ} (h : j + 1 + 1 ≤ D.R.m) :
    FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j = D.host.AA * D.host.AAbar⁻¹ * cI D (j + 1 + 1) := by

  have h1 : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
  have h2 : (D.R.m - j) / 2 = (D.R.m - (j + 1 + 1)) / 2 + 1 := by omega
  rw [cI, cI, h1, h2, pow_succ, pow_succ, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
  ring

theorem idV_mono {𝔞 𝔟 : FI D} (h : 𝔞 ≤ 𝔟) (v : Pl D) : idV 𝔞 v ≤ idV 𝔟 v := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, hv, x, hx, rfl⟩
  exact ⟨α, hα, hv, x, h hx, rfl⟩

theorem idV_zero (v : Pl D) : idV (0 : FI D) v = ⊥ := by

  rw [idV, AddSubgroup.closure_eq_bot_iff]
  rintro y ⟨α, -, -, x, hx, rfl⟩
  obtain rfl : x = 0 := by simpa using hx
  simp

theorem YPart.Sk.withT {ζ₀ : Fin a.Lz.rank → D.host.E} {τ} (h : b.Sk ζ₀ τ) (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V)
    (ht : ∀ j, t j ∈ GfC _) : (b.withT t).Sk ζ₀ τ where
  base := by

    have hb := h.base
    exact { hb with t := ht }
  chBF := h.chBF
  chFB := h.chFB
  norm := h.norm
  tau := h.tau

theorem CoreLat.withT {β₀ M} (h : CoreLat o b β₀ M) (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V) :
    CoreLat o (b.withT t) β₀ M := by
  refine ⟨h.sd, ?_, h.split, h.line⟩
  exact h.glued

def GY.withT {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} {G : GX a ζ₀ PP} {τ} (H : GY G b τ)
    (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V) : GY G (b.withT t) τ :=
  ⟨H.FY, H.sc, H.sc_unit, H.sc_step, H.hz_unit, H.bes, H.jac, H.tau⟩

example (h : FactPrincipalDatum) : dI D * ((D.host.ddE : Ideal (𝓞 D.host.E)) : FI D) = 1 := h _ D.host

example (b : YPart a) : b.withT b.t = b := rfl

example (j : ℕ) : bI D j 1 0 = dI D * cI D j := by simp [bI]

example {S S₀ : HSp D} (d : HypDec S S₀ 0) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) :
    MonoId d L L₀ 𝔟 v ↔ MonoAt d L L₀ v :=
  ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealOf
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

def JetS (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (s : ℕ → ℂ) : Prop :=
  ∀ j (hj : j + 1 ≤ B.R.m), s j ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
    pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
      jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) (s j) (ColDat.xiS θ j hj f) P

def lowOf : (FrN (I.rec7 l Z) (B.R.N B.R.m) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :=
  fnOf _ (shiftOf (sgT (D := I.rec7 l Z) u)) 1 ∘ₗ (I.perIn u I.mu0).br B.fields.emb B.embLL (B.hcW u) ∘ₗ
    Formalism.L2.Col.polOf _ (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩

variable {I l Z} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))

@[reducible] def realOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : RealD (commOf R u g) where
  N := B.R.N
  hN := rankN (I.rec7 l Z)
  NT := B.R.N B.R.m - 1
  hT := rankP (I.rec7 l Z)
  fr := fun _ => ⟨fun y => ⟨y.1, y.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  lam := Formalism.L2.Forms.lamT (D := I.rec7 l Z) u
  n := fun j τ => (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ + (I.chain l u I.mu0).sSharp j τ).toNat
  sS := (I.chain l u I.mu0).sSharp
  sD := (I.chain l u I.mu0).sDiv
  sc := fun j τ => if s j = 0 then 1 else s j / I.J.cD τ
  BT := fun _ => 1
  sg := sgT (D := I.rec7 l Z) u
  J := J
  low := fun _ h => Eq.rec (motive := fun n _ => (FrN (I.rec7 l Z) (B.R.N n) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ))
    (lowOf I l Z u) h.symm

def JOf (j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ))
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : Prop :=
  ∀ v, ∀ k ∈ GinfC (I.rec7 l Z).sp.X', ∀ z z' : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
    IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' → J v k z' = j v ⟨z.1, z.2⟩

variable (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) {a : I.ι} (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) (A : TwDat I l Z u a k.Ch) :
    ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := A.U
  chi := A.chi
  h := A.h
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinCh (c₀ : ℕ → ℂ) (A : TwDat I l Z u a k.Ch) (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColT A R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (p : ι → SplitPt (I.rec7 l Z) k)
    (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)) : Prop :=
  (∃ e : ι ≃ (B.primes X).vT u, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (e i).1) ∧
    ∀ j, j ≤ B.R.m → (∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) ∧ ∀ i, (β j i).IsLat (L j) (Q j i).lat ∧
      ∀ z ∈ L j, ∀ r : Fin ((I.rec7 l Z).sp.X j).rank, r.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∃ s : 𝒪[k],
        (s : k) = (p i).pr (incA (I.rec7 l Z) ((show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)) * z r)) ∧
        (Q j i).HasVal ((β j i).b' *ᵥ fun r' => (p i).pr (incA (I.rec7 l Z) (z r'))) (residue 𝒪[k] s)

def StdEx : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ), IsStdChar (I.rec7 l Z) ψ (-1) →
    ∀ L : ∀ j, Lat ((I.rec7 l Z).sp.X j), (∀ j, j ≤ B.R.m → ∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) →
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
      (p : ι → SplitPt (I.rec7 l Z) k) (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle)
      (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
      (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
      Places p J (fun x => ∃ i, x = (p i).v) ∧ (∀ i, HasConductor (χ i) 1 ∧ (p i).IsChar ψ (χ i)) ∧ resCard k = B.T u ∧
      (∀ i, valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)))) =
          valuation k ((q.1 : 𝒪[k]) : k) ∧
        valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)))) = 1) ∧
      (∀ x : Pl (I.rec7 l Z), (∃ i, x = (p i).v) ↔ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ x.asIdeal) ∧
      (∀ j i, (β j i).b = 1) ∧ StdT I l Z u p β Q L

def TwLev : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ j, j ≤ B.R.m → ∀ b,
      (∀ i g, g • Q j i = Q j i → ∃ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1) ∧
      ∀ κ ∈ A.U j b, ∃ g : ι → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ i, g i • Q j i = Q j i) ∧
        ∃ κ' ∈ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β j i).gl (g i)).prod * κ'

def TwRam : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y)) ∧ (RamT (I := I) (l := l) (u := u) (a := a) j φ ↔ ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y))

def TwTrans : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∃ φ' ∈ (I.fm l u a).Fi j, ∀ b y, A.rd θ j hj b φ' y = trc c (A.rd θ j hj b φ y)

def TwS : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1),
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ →
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧
      ∀ η, RamT (I := I) (l := l) (u := u) (a := a) j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y)

def TwVec : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ ψ θ x vac c₀, PinX I l Z ψ θ x vac c₀ →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
    StdT I l Z u p β Q (fun j => (x j).L) → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) α γ (cT : WO _ _ →₀ ℂ),
      Reps ψ (β j) (β (j + 1)) (x j).L (x (j + 1)).L (fun i => phiOne (Q j i) (Q (j + 1) i)) J (fun v => ∃ i, v = (p i).v) cT →
      ∀ e : AE (I.rec7 l Z), IsIdemSum e ((B.primes X).vT u) →
        IsRatDatum ψ _ _ e (fun z => B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z))) (vac j)
          (comb ψ _ _ cT (vac j))

end GlobalTheory.AdForm

end
end


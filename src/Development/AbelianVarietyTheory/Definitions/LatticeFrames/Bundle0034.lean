import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamCol
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

def TwStd (W : RealPack ex) : Prop :=
  ∃ (l0 : I.Law0 l) (t : SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols (I.tw l l0 Z)),
    ex.tw = I.tw l l0 Z ∧ HEq W.R.T.tw t ∧ I.StdTw l Z l0 t

def FamCol {W : RealPack ex} {u : (I.rec7 l Z).what₂.Word} (f : FamCh W u) : Prop :=
  ∃ c₀, PinX I l Z (pk W).ψ (pk W).θ f.g.x f.g.vac c₀ ∧ ∀ t : W.P.T,
    (∃ (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) (ι : ∀ j, (f.col t).Ch j → Ch₀ j) (w : _),
      PinChL (pk W) f.g (f.col t) c₀ A ι w) ∧
    ∃ UT ε, PinTopL (pk W) f.g (lvP W) (t := t) (f.col t) UT ε

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

def Framed (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam : D.host.E, μ ≠ 0 ∧ (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧
    (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧
    (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧
    ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k))

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsPairResThetaInt
section
noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.OrthSumSp (posSp hypSp hypSumDec posSp_sigOK hypSp_sigOK)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW.WeakModel

variable {D : D7}

def IsPairRes {S T' : HSp D} (ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (m : Measure (GA D T'))
    (Ψ : WO S T' → ℂ) (B : GA D S → ℂ) : Prop :=
  ∃ (E : GA D T' → ℂ → ℂ) (c : ℂ → ℂ) (s₀ : ℂ) (σ : ℝ), (∀ s : ℂ, σ < s.re → ∀ g, ThetaPairConv ω' m Ψ (fun h => E h s) g) ∧
    ∀ g, ResidueAt (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) s₀ (B g)

theorem residueAt_zero (s₀ : ℂ) : ResidueAt (fun _ : ℂ => (0 : ℂ)) s₀ 0 :=
  ⟨_, isExtAt_const 0 s₀, laurentConst_of_tendsto (by simp)⟩

theorem IsPairRes.eq_zero {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} {B : GA D S → ℂ} (h : IsPairRes ω' m Ψ B) {g : GA D S} (h0 : ∀ x, thetaKO ω' g x Ψ = 0) : B g = 0 := by
  obtain ⟨E, c, s₀, σ, -, hr⟩ := h
  have e : (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) = fun _ => 0 := funext fun s => by
    have : (descend (GQ T') fun h => thetaKO ω' g h Ψ * E h s) = fun _ => 0 := funext fun q => by simp [AutomorphicL2Unitary.descend, h0]
    simp [thetaPair, this]
  have := hr g
  rw [e] at this
  exact CoeffAt.unique this (residueAt_zero s₀)

theorem IsPairRes.eq_of_kernel {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} {B : GA D S → ℂ} (h : IsPairRes ω' m Ψ B) {g g' : GA D S}
    (h0 : ∀ x, thetaKO ω' g x Ψ = thetaKO ω' g' x Ψ) : B g = B g' := by
  obtain ⟨E, c, s₀, σ, -, hr⟩ := h
  have h1 := hr g
  have h2 := hr g'
  unfold thetaPair at h1 h2
  simp only [h0] at h1
  exact CoeffAt.unique h1 h2

theorem isPairRes_thetaInt {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} (h : ∀ g, ThetaPairConv ω' m Ψ 1 g) (κ : ℂ) : IsPairRes ω' m Ψ (κ • thetaInt ω' m Ψ) := by
  refine ⟨fun _ _ => 1, fun s => κ * s⁻¹, 0, 0, fun _ _ g => h g, fun g => ?_⟩
  have h3 : IsMerExt (fun s : ℂ => κ * s⁻¹ * thetaInt ω' m Ψ g) Set.univ fun s => κ * s⁻¹ * thetaInt ω' m Ψ g :=
    ⟨isRightDomain_univ, fun s _ => by fun_prop, 0, fun s _ => rfl⟩
  refine (h3.isExtAt trivial).coeffAt_of_tendsto (k := 1) (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_))
  have : s ≠ 0 := hs
  simp only [Pi.smul_apply, smul_eq_mul, sub_zero, pow_one]
  field_simp

def Met (A T T' : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ))
    (ω' : GA D (dblSp A) × GA D T' →* Module.End ℂ (WO (dblSp A) T' → ℂ)) (a : GL (Fin A.rank) (AE D))
    (μ₀ : Measure (WO A T)) (𝓕₀ : Set (WO A T)) (m : Measure (GA D T')) (φ : WO (dblSp A) T → ℂ),
    IsWeilDatumO ψ (dblSp A) T 1 χ ω ∧ IsWeilDatumO ψ (dblSp A) T' 1 χ ω' ∧ m.IsHaarMeasure ∧ IsCovolOne (ratL T A) μ₀ 𝓕₀ ∧
    swSec A T ω μ₀ 𝓕₀ φ 1 = 1 ∧
    ∃ (Ψ : WO (dblSp A) T' → ℂ) (B : GA D (dblSp A) → ℂ), IsThetaFunO ψ (dblSp A) T' Ψ ∧ IsKFinVec ω' (Khat A a) Ψ ∧
      IsPairRes ω' m Ψ B ∧ EisCoeffAt A (flat A a (swSec A T ω μ₀ 𝓕₀ φ) (sZero A T)) (sZero A T) (-1) B

theorem met_of (h : FirstTermWeak) (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (hA : HSpace.SigOK A) (hT : HSpace.SigOK T)
    (hr : T.rank + T'.rank = 2 * A.rank) (hlt : T'.rank < T.rank) (h0 : 0 < T'.rank)
    (hc : IsAniso T' ∨ ∃ (T₀ : HSp D) (r' : ℕ) (_ : HypDec T' T₀ r'), IsAniso T₀ ∧ 0 < r') : Met A T T' := by
  obtain ⟨ψ, χ, ω, a, θ, sS, sT, ν, 𝓕, -, φ, hω, ha, hθ, hS, hsT, hK, hν, -, hφ, h1⟩ :=
    GlobalTheory.Core.Rk.IP.FockModel.hyp A T hA hT (by omega) (by omega)
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨ω', hω'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hω.std (dblSp A) T' 1 χ ⟨η, hη⟩ hω.hecS hω.hecT hω.resS
    (resEta_parity hω.resT (by omega))
  obtain ⟨b, hb⟩ := exists_isMaj T
  obtain ⟨b', hb'⟩ := exists_isMaj T'
  have h2 := fun v => GlobalTheory.Core.Rk.IP.Model.isSplit_two (D := D) v
  obtain ⟨Ψ, B, p1, p2, p3, p4⟩ := h D ψ A T T' t d hr hlt h0 χ ω ω' hω hω' a b ha hb (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)
    (GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D T T' t d b h2 hb) ν 𝓕 hν Measure.haar inferInstance θ hθ sS sT hS hsT hK
    (hc.imp_right fun ⟨T₀, r', d₀, e1, e2⟩ => ⟨T₀, r', d₀, b', e1, e2, hb', GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D T' T₀ r' d₀ b' h2 hb'⟩)
    φ hφ (GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ _ T 1 χ ω sS sT hω hθ hS hsT _ (isCompact_Khat A a) hK φ hφ)
  exact ⟨ψ, χ, ω, ω', a, ν, 𝓕, Measure.haar, φ, hω, hω', inferInstance, hν, h1, Ψ, B, p1, p2, p3, p4⟩

theorem isAniso_pos (D : D7) (n : ℕ) : IsAniso (posSp D n) :=
  GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite _ (posSp_sigOK D n) fun _ => .inl rfl

theorem met_aniso (h : FirstTermWeak) (D : D7) : Met (posSp D 2) (hsum (posSp D 1) (hypSp D 1)) (posSp D 1) :=
  met_of h _ _ _ 1 (hypSumDec D _ 1) (posSp_sigOK D 2) (sigOK_hsum (posSp_sigOK D 1) (hypSp_sigOK D 1)) rfl
    (by show 1 < 1 + (1 + 1); omega) Nat.one_pos (.inl (isAniso_pos D 1))

theorem met_iso (h : FirstTermWeak) (D : D7) :
    Met (posSp D 4) (hsum (hsum (posSp D 1) (hypSp D 1)) (hypSp D 1)) (hsum (posSp D 1) (hypSp D 1)) :=
  met_of h _ _ _ 1 (hypSumDec D _ 1) (posSp_sigOK D 4)
    (sigOK_hsum (sigOK_hsum (posSp_sigOK D 1) (hypSp_sigOK D 1)) (hypSp_sigOK D 1)) rfl
    (by show 1 + (1 + 1) < 1 + (1 + 1) + (1 + 1); omega) (by show 0 < 1 + (1 + 1); omega)
    (.inr ⟨_, 1, hypSumDec D _ 1, isAniso_pos D 1, Nat.one_pos⟩)

end GlobalTheory.RegSW.WeakModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw

section Sign
variable {D : D7} {c : Comm D} {t : Tup c}

def twist (w : VTup t) (s : ∀ j, t.Ch j → ℂ) : VTup t :=
  { w with
    dQ := fun j α γ => (s j α * s (j + 1) γ) • w.dQ j α γ
    ε := fun j α => s j α • w.ε j α
    εT := fun n h β => s n β • w.εT n h β }

def QPinS (v : VCom c) (w : VTup t) : Prop :=
  ∃ (w₀ : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, s j α ^ 2 = 1) ∧ QPin v w₀ ∧ w = twist w₀ s

theorem twist_one (w : VTup t) : twist w (fun _ _ => 1) = w := by
  cases w; simp [twist]

theorem QPinS.of {v : VCom c} {w : VTup t} (h : QPin v w) : QPinS v w :=
  ⟨w, fun _ _ => 1, fun _ _ => one_pow _, h, (twist_one w).symm⟩

example (w : VTup t) (j α γ) : (twist w fun _ _ => -1).dQ j α γ = w.dQ j α γ ∧ (twist w fun _ _ => -1).ε j α = -w.ε j α := by
  simp [twist]

variable {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}

def QGeo.Res (G : QGeo v B PP) (δ : G.kˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ (z : 𝓞 D.host.E) (x : G.kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), (x : G.k) = (ofSplit G.q).pr (z : D.host.E) →
    (r : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ r)⁻¹

def QExt.tw {G : QGeo v B PP} {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) : GlobalTheory.TwBridge.TwData G.k :=
  ⟨G.ϖ, G.unif, G.ψk, hψ, G.cond, E.δ, E.tame, E.η, E.unr, sg⟩

structure QGeo.FrTie (G : QGeo v B PP) (fr : ∀ i, i ≤ D.R.m → Matrix (Fin (c.X i).rank) (Fin (D.R.N i)) D.host.E) : Prop where
  frX : ∀ i (hi : i ≤ G.s + 1) (hm : i ≤ D.R.m), ∃ e : XIx (Fin D.R.k) (Fin D.R.t) i ≃ Fin (D.R.N i),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e ∧ ∀ r a, (G.FX i hi).β r a = (ofSplit G.q).pr (fr i hm r (e a))
  frM : ∀ hm : G.s + 1 + 1 ≤ D.R.m, ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2) ⊕ Unit ≃ Fin (D.R.N (G.s + 1 + 1)),
    GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => D.R.N D.R.m - 1) e ∧
      ∀ r a, G.FM.β r a = (ofSplit G.q).pr (fr (G.s + 1 + 1) hm r (e a))

theorem exists_xOrd (R : Ranks) (j : ℕ) :
    ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := by
  have h : R.k + j + j * R.t = R.N j := by
    show _ = R.k + j * (R.t + 1)
    ring
  refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr h), ?_⟩
  rintro ((i | i) | ⟨p, q⟩) <;> simp [GlobalTheory.SymBridge.xPos, finProdFinEquiv]
  ring

theorem exists_topOrd (R : Ranks) (s : ℕ) (hs : s + 1 + 1 = R.m) :
    ∃ e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N (s + 1 + 1)),
      GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => R.N R.m - 1) e := by
  have h : R.k + (s + 1) + (s + 2) * R.t + 1 = R.N (s + 1 + 1) := by
    show _ = R.k + (s + 1 + 1) * (R.t + 1)
    ring
  refine ⟨((Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv)
    finOneEquiv.symm).trans finSumFinEquiv).trans (finCongr h), ?_⟩
  rintro (((i | i) | ⟨p, q⟩) | i)
  · simp [GlobalTheory.SymBridge.zPos]
  · simp [GlobalTheory.SymBridge.zPos]
  · simp [GlobalTheory.SymBridge.zPos, finProdFinEquiv]
    ring
  · simp [← hs, ← h]

end Sign

section True
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)

abbrev BadPr (I : TC B X) (a : I.ι) : Type := Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)

def locLast (I : TC B X) (a : I.ι) (P : BadPr I a) : ∀ (i : ℕ), i + 1 = B.R.m →
    Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → Formalism.L2.Col.Sp B.fields.E (B.R.N i) → B.fields.K
  | 0, h => absurd B.R.two_le_m (by omega)
  | n + 1, h => fun y y' => TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P (castSp B.fields.E (congrArg B.R.N h) ∘ₗ y) y'

def locXi (i : ℕ) (α : Ch₀ i) (γ : Ch₀ (i + 1)) (P : BadPr I a)
    (x : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : B.fields.K :=
  let y := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (i + 1) γ).1.1 P) x
  if h : i + 2 < B.R.m then
    Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i ((A.b0 i α).get (by omega)) P)
      ((I.idx a).h (i + 1) ((A.b0 (i + 1) γ).get (by omega)) P) y
  else if h : i + 2 = B.R.m then
    Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i ((A.b0 i α).get (by omega)) P) y
      ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (i + 1) γ).1.1 P).symm (Formalism.L2.Col.repY (A.p0 (i + 1) γ).1.2))
  else if h : i + 1 = B.R.m then
    locLast I a P i h y ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i α).1.1 P).symm (Formalism.L2.Col.repY (A.p0 i α).1.2))
  else 0

abbrev homOf (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) :=
  toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z

def xiOff (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (Formalism.L2.Col.phiT B.fields.K (A.p0 i α).1.1.deco.1 (A.p0 (i + 1) γ).1.1.deco.1 (homOf I l Z i hi z) *
    ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∈ (B.primes X).vGs), locXi A i α γ P (homOf I l Z i hi z))

theorem xi_eq_xiOff_mul (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1)) (z) :
    A.xi i hi α γ z = xiOff A i hi α γ z *
      B.embLL (∏ P ∈ Finset.univ.filter (fun P : BadPr I a => ¬ P.1 ∈ (B.primes X).vGs), locXi A i α γ P (homOf I l Z i hi z)) := by
  rw [xiOff, ← map_mul, mul_assoc, Finset.prod_filter_mul_prod_filter_not, TwDat.xi]
  congr 1
  unfold xiAt locXi
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := B.R.two_le_m; omega⟩
    rfl
  · omega

def BaseCommon : Prop := ∀ i, i ≤ B.R.m → ∀ β β', (A.p0 i β).1.1 = (A.p0 i β').1.1 ∧ A.kA i β = A.kA i β' ∧ A.xr i β = A.xr i β'

def baseFr (P : BadPr I a) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r b =>
  Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single b 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

def BaseMoved : Prop := ∀ i, i ≤ B.R.m → ∀ β β',
  (A.p0 i β).1.1.deco = (A.p0 i β').1.1.deco ∧ (i + 1 ≠ B.R.m → (A.p0 i β).1.1 = (A.p0 i β').1.1)

theorem BaseCommon.moved (h : BaseCommon A) : BaseMoved A :=
  fun i hi β β' => ⟨congrArg _ (h i hi β β').1, fun _ => (h i hi β β').1⟩

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle}

structure ReadsAt (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop where
  eq : P.1 = PP
  tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  rep : ∀ j d (h : j + d = G.s) (hj : j < B.R.m) β, GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z)))
    ((I.idx a).h j ((A.b0 j β).get hj) P) (E.rep j d h (π j β))

variable (G) in

def ownVec (P : BadPr I a) (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))) (β : Ch₀ (G.s + 1)) :
    XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k := fun r => (ofSplit G.q).pr
  ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (G.s + 1) β).1.1 P).symm (Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2) (e r))

structure ReadsOrb (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop
    extends ReadsAt A P E hψ sg π where
  orb : ∀ β (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
    SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (E.cos (π (G.s + 1) β))
      (Submodule.Quotient.mk (ownVec A G P e β))

structure MovedAt (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop
    extends ReadsAt A P E hψ sg π where
  rk : ∀ i, (c.X i).rank = ((I.rec7 l Z).sp.X i).rank
  low : ∀ i (hi : i ≤ G.s) (hm : i ≤ B.R.m) β (e : XIx (Fin B.R.k) (Fin B.R.t) i ≃ Fin (B.R.N i)),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r b,
      (ofSplit G.q).pr (baseFr A P i hm β (Fin.cast (rk i) r) (e b)) = (G.FX i (Nat.le_succ_of_le hi)).β r b
  pen : ∀ (hm : G.s + 1 ≤ B.R.m) β (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∃ κ ∈ ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J,
      (∀ r b, (ofSplit G.q).pr (baseFr A P (G.s + 1) hm β (Fin.cast (rk _) r) (e b)) =
        ((G.FX (G.s + 1) le_rfl).β * κ.val.toBlocks₁₁) r b) ∧
      E.cos (π (G.s + 1) β) = Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ ownVec A G P e β)

variable {A}

variable (A)

theorem ownVec_mem (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (hc : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ) (e) (β) :
    ownVec A G P e β ∈ box _ (G.ϖ ^ (I.cst a).M)⁻¹ := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have h0 := (A.p0 (G.s + 1) β).repY_mem hs
  obtain ⟨y, hy, hY⟩ := (A.p0 (G.s + 1) β).mem_ybSet hs
  set z := Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2 with hz
  rw [hY] at h0
  have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy P
  have h2 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 h0 P
  simp only [if_neg hP] at h1 h2
  have hq : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := fun h => G.ϖ.ne_zero (by rw [hc.unif, h, map_zero])
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.p0 (G.s + 1) β).1.1.deco.1.N := by
    have h4 := add_mem h1 (Submodule.smul_mem _ (((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) ^ (2 * (I.cst a).M)) h2)
    convert h4 using 1
    rw [← algebraMap_smul B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) ^ (2 * (I.cst a).M)), smul_smul, map_pow, map_natCast,
      _root_.zpow_neg, inv_inv, zpow_natCast, two_mul, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one, ← smul_add, add_sub_cancel]
  rw [← (ptFr (A.p0 (G.s + 1) β).1.1 P.1).apply_symm_apply (_ • z)] at h3
  have h5 := (isFr_ptFr (A.p0 (G.s + 1) β).1.1 P.1 _).1 h3
  rw [← frsF_eq_ptFr I.sel (I.tup a), map_smul] at h5
  intro r
  have h6 := (hc.int _).2 (GlobalTheory.TopStep.mem_stdAt.1 h5 (e r))
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul] at h6
  have h7 : 0 < valuation G.k ((G.ϖ : G.k) ^ (I.cst a).M) := by
    rw [map_pow]
    exact pow_pos ((Valuation.pos_iff _).2 G.ϖ.ne_zero) _
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, ← mul_one (_⁻¹), le_inv_mul_iff₀ h7]
  exact h6

end True

end GlobalTheory.QTw
end
end


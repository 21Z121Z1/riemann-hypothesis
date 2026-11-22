import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopLocData

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

def reN {N N' : ℕ} (h : N = N') (F : Frame k N Y) : Frame k N' Y := h ▸ F

@[simp] theorem reN_rfl {N : ℕ} (F : Frame k N Y) : reN rfl F = F := rfl

theorem exists_o {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁ : SB (Matrix Y Y' k), IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hT a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hT

def mkPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hu : q.UnitAA)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : SB (Matrix Y Y' k)) (e : WO S T →₀ ℂ)
    (he : (ofSplit q).IsCombAt ψ FS FT e Φ.1) {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') : LocPl ψ S T M M' :=
  ⟨k, q, hu, Y, Y', FS, FT, Φ, e, he, Classical.choose (exists_o hψ q FS FT hS hT),
    (Classical.choose_spec (exists_o hψ q FS FT hS hT)).1, (Classical.choose_spec (exists_o hψ q FS FT hS hT)).2⟩

end Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
  {v : VCom f.c}

theorem s_eq (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) : G.s = j := by
  have := G.hs; omega

def frS (G : GLoc v) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    Frame G.k (Yc D (j + 1)).rank (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) :=
  reN (congrArg (fun s => (Yc D (s + 1)).rank) (s_eq G h)) (G.FY (G.s + 1) 0 rfl)

def phiT (G : GLoc v) : SB (Matrix (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0) G.k) :=
  ⟨(G.S.T (Fin D.R.t)).PhiTop, (GModel.phi_sb G).2⟩

theorem isCombAt_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k)
    (ψ : AddChar (AF D.host.F) ℂ) (FT : Frame k D.sp.X'.rank Y) (Ξ : Matrix Y Y' k → ℂ) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y') (e : WO (Yc D (s + 1)) D.sp.X' →₀ ℂ)
      (e' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), HEq e' e → (ofSplit q).IsCombAt ψ F FT e Ξ →
      (ofSplit q).IsCombAt ψ (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) FT e' Ξ := by
  rintro s j rfl F e e' he h
  cases he
  exact h

theorem intIn_reN {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y' : Type} [Fintype Y'] [DecidableEq Y'] (q : GlobalTheory.FinPl.SplitPt D k) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) :
    ∀ {s j : ℕ} (hs : s = j) (F : Frame k (Yc D (s + 1)).rank Y'), IntIn q (Yc D (s + 1)) F (N (s + 1)) →
      IntIn q (Yc D (j + 1)) (reN (congrArg (fun s => (Yc D (s + 1)).rank) hs) F) (N (j + 1)) := by
  rintro s j rfl F h
  exact h

def eT {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    WO (Yc D (j + 1)) D.sp.X' →₀ ℂ :=
  Classical.choose (hGP.eGT j h) i

theorem eT_spec {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) :
    (∀ i, HEq (eT hGP h i) (G i).egT) ∧ ∀ F, IsThetaFunO f.c.ψ _ _ F →
      comb f.c.ψ _ _ (v.eGT j h) F = (List.finRange n).foldr (fun i g => comb f.c.ψ _ _ (eT hGP h i) g) F :=
  Classical.choose_spec (hGP.eGT j h)

theorem eT_is {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) (i : Fin n) :
    (ofSplit (G i).q).IsCombAt f.c.ψ (frS (G i) h) (G i).FT (eT hGP h i) (phiT (G i)).1 :=
  isCombAt_reN (G i).q f.c.ψ (G i).FT _ (s_eq (G i) h) ((G i).FY ((G i).s + 1) 0 rfl) (G i).egT _
    ((eT_spec hGP h).1 i) (G i).egT_is

def lp (hψ : IsStdChar D f.c.ψ (-1)) {n : ℕ} {G : Fin n → GLoc v} (hGP : GPin G) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m)
    {M : GlobalTheory.FinPl.Lat (Yc D (j + 1))} (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT) (i : Fin n) :
    LocPl f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT :=
  mkPl hψ (G i).q (G i).unit (frS (G i) h) (G i).FT (phiT (G i)) (eT hGP h i) (eT_is hGP h i) hM hLT

end GlobalTheory.TopLocData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

noncomputable section
namespace GlobalTheory.LocMod

def IsLocFac (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (PP : Formalism.L2.DIV.Pl D.host.E) (c : WO S T →₀ ℂ)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k)
    (Y Y' : Type) (_ : Fintype Y) (_ : DecidableEq Y) (_ : Fintype Y') (_ : DecidableEq Y') (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) (Ξk : Matrix Y Y' k → ℂ),
    DenseRange p.pr ∧ Formalism.L2.NTheta.IsIdemAt p.e PP ∧
    (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) ∧
    Ξk ∈ SB (Matrix Y Y' k) ∧ p.IsCombAt ψ FS FT c Ξk ∧ ∀ γ, Ξ γ = Ξk (FT.γ * γ.map p.pr * FS.β)

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

abbrev FYFam {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) : Type :=
  ∀ j c, j + c = l.s + 1 → Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)

def IsNormalFr {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (y : YRat a)
    (FY : FYFam l) (sc : ℕ → l.k) : Prop :=
  (∀ j, valuation l.k (sc j) = 1) ∧ (∀ j, sc (j + 1 + 1) = sc j * (ofSplit l.q).xi) ∧
  (∀ j ρ h, valuation l.k ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1) ∧
  (∀ j ρ h c (hc : j + c = l.s + 1), (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j (by omega))
    (FY j c hc)) ∧
  (∀ j ρ h c (hc : j + 1 + c = l.s + 1), (ofSplit l.q).IsJacFrame ((y.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (l.FX (j + 1) (by omega)) (FY (j + 1) c hc)) ∧
  ∀ h, (y.τ l.s h).map (ofSplit l.q).pr *ᵥ (fun i => (ofSplit l.q).pr (a.ζ₀ i)) =
    (-((ofSplit l.q).xi * sc l.s)) • fun i => (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i)

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SchwartzSch

variable {D : D7}

def volOf {A B : HSp D} (ν : Measure (WO A B)) (𝓨 : Set (WO A B)) (h : IsCovolOne (ratL B A) ν 𝓨) :
    GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, h⟩

theorem continuous_finPart' : Continuous (finPart D) := by
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hec

variable {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A B : HSp D} {ν : Measure (WO A B)}
  {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ} (hf : IsThetaFunO ψ (dblSp A) B f)

include hψ hν hf

theorem sch_level : ∃ U : AddSubgroup (Mx D B.rank A.rank), IsOpen (U : Set (Mx D B.rank A.rank)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, sch ψ A B ν 𝓨 f (x + u) = sch ψ A B ν 𝓨 f x := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  refine ⟨U.comap ((dblDec A).extX B), ?_, ?_⟩
  · have hX : Continuous ((dblDec A).extX B) := continuous_id.matrix_mul continuous_const
    exact hUo.preimage hX
  · intro u hu h0 x
    have h0' : ((dblDec A).extX B u).map (infPart D) = 0 := by
      rw [HypDec.extX_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    have h := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) f hf).1 x u
    rw [hU _ hu h0'] at h
    exact (congrFun h 0).symm

theorem sch_supp : ∃ K : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, sch ψ A B ν 𝓨 f x ≠ 0 → x.map (finPart D) ∈ K := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K, hK, hsupp⟩ :=
    GlobalTheory.Unf.mixS_support_inBox D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) U hUo
  refine ⟨(fun k : Mx D B.rank A.rank => k.map (finPart D)) '' K,
    hK.image (continuous_id.matrix_map continuous_finPart'), ?_⟩
  intro x hx
  have hmem : f ∈ GlobalTheory.Size.thetaLevel ψ (dblSp A) B U := ⟨hf, hU⟩
  obtain ⟨k, hk, hxk⟩ := hsupp f hmem x 0 hx
  refine ⟨k, hk, ?_⟩
  have hs : (x - k).map (finPart D) = x.map (finPart D) - k.map (finPart D) :=
    Matrix.map_sub _ (fun a b => (finPart D).map_sub a b) x k
  rw [hs, sub_eq_zero] at hxk
  exact hxk.symm

theorem sch_schwartz (k : ℕ) (L : (Fin k → ℝ) →+ Mx D B.rank A.rank) (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L)
    (hinj : Function.Injective L) (x : Mx D B.rank A.rank) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = sch ψ A B ν 𝓨 f (x + L t) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let V : Set ((Fin k → ℝ) → ℂ) :=
    {φ | ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ φ = fun t => sch ψ A B ν 𝓨 f' (x + L t)}
  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨f', hf', rfl⟩
    exact (GlobalTheory.T.doubledPairSchrodingerFunction_continuous_integrable D ψ hψ A B ν 𝓨 hν f' hf').1.comp (continuous_const.add hL.1)
  have hder : ∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ t : Fin k → ℝ,
      HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' t) 0 := by
    rintro φ ⟨f', hf', rfl⟩ i
    let M : ℝ →+ Mx D B.rank A.rank :=
      { toFun := fun s => L (s • (Pi.single i (1 : ℝ) : Fin k → ℝ))
        map_zero' := by rw [zero_smul, map_zero]
        map_add' := fun a b => by rw [add_smul, map_add] }
    have hMc : Continuous M := hL.1.comp (continuous_id.smul continuous_const)
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hL.2 _
    obtain ⟨f'', hf'', hd⟩ := GlobalTheory.T.schroedingerFunction_hasDerivAt_real_line_doubledPair D ψ hψ A B ν 𝓨 hν f' hf' M hMc hMf
    refine ⟨fun t => sch ψ A B ν 𝓨 f'' (x + L t), ⟨f'', hf'', rfl⟩, fun t => ?_⟩
    have h := hd (x + L t)
    have he : (fun s : ℝ => sch ψ A B ν 𝓨 f' (x + L (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ)))) =
        fun s : ℝ => sch ψ A B ν 𝓨 f' (x + L t + M s) := by
      funext s
      simp only [map_add, add_assoc]
      rfl
    simp only at h ⊢
    rw [he]
    exact h
  have hdecay : ∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ t, ‖t‖ ^ N * ‖φ t‖ ≤ C := by
    rintro φ ⟨f', hf', rfl⟩ N
    obtain ⟨C₁, hC₁⟩ := (GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation D θ hθ B.rank A.rank k L hL).2 hinj
    obtain ⟨C₂, hC₂⟩ :=
      GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) N
    have hfin := (GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ (dblSp A) B).1 N f' hf'
    have hne : (C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f' ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
    set c : ℝ := |C₁| * (1 + GlobalTheory.Unf.realSize θ x) with hc
    have hc0 : 0 ≤ c := mul_nonneg (abs_nonneg _) (by linarith [GlobalTheory.Unf.realSize_nonneg θ x])
    clear_value c
    refine ⟨c ^ N * ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal, fun t => ?_⟩
    have hy0 := GlobalTheory.Unf.realSize_nonneg θ (x + L t)
    have hx0 := GlobalTheory.Unf.realSize_nonneg θ x
    have h1 : ‖t‖ ≤ c * (1 + GlobalTheory.Unf.realSize θ (x + L t)) := by
      calc ‖t‖ ≤ C₁ * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) := hC₁ x t
        _ ≤ |C₁| * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
        _ ≤ |C₁| * ((1 + GlobalTheory.Unf.realSize θ x) * (1 + GlobalTheory.Unf.realSize θ (x + L t))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
        _ = c * (1 + GlobalTheory.Unf.realSize θ (x + L t)) := by rw [hc]; ring
    have h2 : ‖sch ψ A B ν 𝓨 f' (x + L t)‖ * (1 + GlobalTheory.Unf.realSize θ (x + L t)) ^ N ≤
        ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal := by
      have h := hC₂ f' hf' (x + L t) 0
      change ‖sch ψ A B ν 𝓨 f' (x + L t)‖ₑ * _ ≤ _ at h
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h
    calc ‖t‖ ^ N * ‖sch ψ A B ν 𝓨 f' (x + L t)‖
        ≤ (c * (1 + GlobalTheory.Unf.realSize θ (x + L t))) ^ N * ‖sch ψ A B ν 𝓨 f' (x + L t)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 N) (norm_nonneg _)
      _ = c ^ N * (‖sch ψ A B ν 𝓨 f' (x + L t)‖ * (1 + GlobalTheory.Unf.realSize θ (x + L t)) ^ N) := by
          generalize ‖sch ψ A B ν 𝓨 f' (x + L t)‖ = a
          generalize GlobalTheory.Unf.realSize θ (x + L t) = s
          rw [mul_pow]; ring
      _ ≤ c ^ N * ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hc0 N)
  have hS := (GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz k V hcont hder).2 hdecay _ ⟨f, hf, rfl⟩
  exact hS

omit hψ hν hf in

theorem isSchwartzBruhat_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (sch ψ A B ν 𝓨 f) := by
  intro D ψ hψ A B ν 𝓨 hν f hf
  exact ⟨sch_level hψ hν hf, sch_supp hψ hν hf, fun k L hL hinj x => sch_schwartz hψ hν hf k L hL hinj x⟩

end GlobalTheory.SchwartzSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitPlaceProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_splitPlace_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  first | exact @GlobalTheory.SplitSBProd.isSBHalf_splitProd | exact GlobalTheory.SplitSBProd.isSBHalf_splitProd | (intros; apply GlobalTheory.SplitSBProd.isSBHalf_splitProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  first | exact @GlobalTheory.ItOnto.kfinSpan_le_span_it | exact GlobalTheory.ItOnto.kfinSpan_le_span_it | (intros; apply GlobalTheory.ItOnto.kfinSpan_le_span_it <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeChainStandardPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLineStd

theorem aaOf_top (D : D7) : (Formalism.L2.PairingIndexBounds.F.aaOf D ⊤) = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  GlobalTheory.Mem.Col2.Th.perAA_top D.host

theorem thetaSpace_std_eq_line : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))), ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := by
  intro B X I l Z w i hi F hF
  let Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ := GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V
  have hS : Bk.StdOK := GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _)
    ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 w.ok.amb_ok.delta)
  have hZ : I.J.V.thZero (B.R.N i) (B.R.N (i + 1)) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := rfl
  have hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) (Formalism.MainNotions.TaylorLogMetric.tor0 (I.rec7 l Z) ⊤ I.J.δ) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := by
    rw [← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, aaOf_top]
    rfl
  have hH : (HV (ι := (I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) :=
    Formalism.L2.KerInert.RepComb.HV_eq_formV _
  rw [hLa, alV, hH] at hF
  have hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1)))) := by
    refine Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := Bk.qInt0 hS _ _ x hx
    exact (Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm
  obtain ⟨c, hc⟩ := Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'
  refine ⟨c, ?_⟩
  have hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := rfl
  obtain ⟨x, hx, hI⟩ := GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))
  have hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) :=
    funext fun z => (Bk.thZeroMem hS _ _).2 x hx z
  have hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := by
    unfold Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf
    rw [hI, hI, hfix, hfix]
  rw [hM, hMz]
  exact hc

end GlobalTheory.ThetaLineStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawsRescaleWithS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (s : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (s • f) = s • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7} {m n : ℕ}

theorem dRho_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (s : ℂ) (f : Mx D m n → ℂ) :
    Datum.dRho hs θ τ z (s • f) = s • Datum.dRho hs θ τ z f := by
  funext x
  simp only [Datum.dRho, hh, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field _

theorem aPlusAll_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k) (s : ℂ) (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (s • f) = s • aPlusAll hs θ J B B' k f := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hh, smul_sub, smul_comm s]

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (k : ι →₀ ℕ) (s : ℂ) (f : X → ℂ) : opPow A k (s • f) = s • opPow A k f := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (s : ℂ) (f : X → ℂ) : pureTensorL A (s • f) = s • pureTensorL A f := by
  unfold pureTensorL
  have : (fun k : ι →₀ ℕ => opPow A k (s • f)) = s • fun k => opPow A k f := by
    funext k; exact opPow_smul A hA k s f
  rw [this, map_smul]

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (s : ℂ) (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (s • f) = s • pureTensorO ψ θ S T sS sT BS BT f :=
  pureTensorL_smul _ (aPlusAll_smul _ (heisO_smul ψ S T) _ _ _ _) s f

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

end GlobalTheory.SeeSaw.Resc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelTwistPlaceInThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.ChainTw.linModel_theta : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  intro D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne s.V s'.V
  obtain ⟨hW, hΦ, T, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P m X hX
  exact ⟨_, hW, hΦ, T, h1, h2, h3⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  first | exact @GlobalTheory.SeeSaw.kerX_of_clsPinD | exact GlobalTheory.SeeSaw.kerX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.kerX_of_clsPinD <;> assumption)
end


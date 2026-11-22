import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
section
noncomputable section
namespace GlobalTheory.Core.Rk.IP.FockModel
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem of_all (D : D7) (h : SiegelWeilAll D) : SiegelWeilFock D :=
  fun ψ A B ha hab hw χB omh hom a hmaj θ sS sB hθ hS hB hc ν 𝓕 hν mH hm φ hφ =>
    h ψ A B ha hab hw χB omh hom a hmaj ν 𝓕 hν mH hm φ hφ.1
      (isKFinVec_of_isFockVec D ψ θ _ B 1 χB omh sS sB hom hθ hS hB _ (isCompact_Khat A a) hc φ hφ)

theorem resEta_one_dbl (A : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) : ResEta D 1 (dblSp A).rank :=
  ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (A.rank + A.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def Hyp (A B : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B) (a : GL (Fin A.rank) (AE D))
    (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (mH : Measure (GA D B)) (φ : WO (dblSp A) B → ℂ),
    IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ IsMaj A a ∧ IsInfFam θ ∧
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) ∧
    IsCovolOne (ratL B A) ν 𝓕 ∧ mH.IsHaarMeasure ∧ IsFockVec ψ θ (dblSp A) B sS sB φ ∧ swSec A B omh ν 𝓕 φ 1 = 1

theorem hyp (A B : HSp D) (hA : HSpace.SigOK A) (hB : HSpace.SigOK B) (ha : 1 ≤ A.rank) (hab : A.rank < B.rank) :
    Hyp A B := by
  obtain ⟨ψ, θ, χA, χB, sA, sB, cA, a, om, ν, 𝓕, Φ, hP, hΦ, h1, -⟩ := Model.exists_pair_unram A B hA hB ha
    (t := B.rank - A.rank) (by omega) (by omega) _ _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat B)
  obtain ⟨-, -, -, hθ, -, -, hsA, hsB, -⟩ := hP.setting
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨omh, homh⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hP.weil.std (dblSp A) B 1 χB ⟨η, hη⟩
    ⟨continuous_const, fun _ => rfl⟩ hP.weil.hecT (resEta_one_dbl A hP.weil.resT) hP.weil.resT
  obtain ⟨c1, c2⟩ := Cartan.cartan_dbl D θ A sA a hθ hsA hP.maj_eq
  refine ⟨ψ, χB, omh, a, θ, _, sB, ν, 𝓕, Measure.haar, delta A B Φ Φ, homh, hP.maj, hθ, c1, hsB, c2, hP.covol,
    inferInstance, GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ A B sA sB hP.weil.std hθ Φ Φ hΦ hΦ, ?_⟩
  have e1 : omh (1, 1) = 1 := map_one omh
  have e2 : om (1, 1) = 1 := map_one om
  simp only [wcoef, e2, Module.End.one_apply] at h1
  simp only [swSec, e1, Module.End.one_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta, h1]

theorem hyp_definite (D : D7) {n m : ℕ} (hn : 1 ≤ n) (hm : n < m) :
    ∃ A B : HSp D, A.rank = n ∧ B.rank = m ∧ wittIndex B = 0 ∧ Hyp A B :=
  ⟨Inh.P D n, Inh.P D m, rfl, rfl, wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.ThetaMean.Model.isAniso_posSpace _),
    hyp _ _ (Examples₂.posSpace_sigOK _ _) (Examples₂.posSpace_sigOK _ _) hn hm⟩

theorem hyp_indefinite (D : D7) : ∃ A B : HSp D, 1 ≤ A.rank ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
    A.rank + wittIndex B < B.rank ∧ (∀ τ, B.sig τ = (8, 1)) ∧ HSpace.SigOK B ∧ Hyp A B := by
  have h := Examples₂.lorentzSpace_signature_ok (E := D.host.E) Examples₂.star_isIntegral
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral) ≤ 1 :=
    (WittSignature.wittIdx_le_signature _ _ h D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  refine ⟨Inh.P D 5, Examples₂.lorentzSpace Examples₂.star_isIntegral, (by decide : 1 ≤ 5), (by decide : 5 < 8 + 1),
    (by decide : 8 + 1 ≤ 2 * 5), ?_, fun _ => rfl, h,
    hyp _ _ (Examples₂.posSpace_sigOK _ _) h (by decide : 1 ≤ 5) (by decide : 5 < 8 + 1)⟩
  rw [← GlobalTheory.RallisIP.wittIdx_eq_wittIndex]
  exact (Nat.add_le_add_left h1 5).trans_lt (by decide : 5 + 1 < 8 + 1)

theorem conclusion_zero (A B : HSp D) (hab : A.rank < B.rank) (omh : WRep (dblSp A) B) (a : GL (Fin A.rank) (AE D))
    (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (mH : Measure (GA D B)) :
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 0) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH 0) := by
  have := GlobalTheory.ThetaMean.Model.conclusion_zero A B omh a ν 𝓕 mH
  rwa [if_pos hab, one_smul] at this

end GlobalTheory.Core.Rk.IP.FockModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NonemptyOffDatOfTrueD
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffInh

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

def reindex {p : SplitPt D k} {S : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (β : Frame p S n) (e : n' ≃ n) : Frame p S n' where
  b := β.b.submatrix id e
  b' := β.b'.submatrix e id
  bb' := (Matrix.submatrix_mul_equiv β.b β.b' id e id).trans (by rw [β.bb', Matrix.submatrix_id_id])
  b'b := (Matrix.submatrix_mul_equiv β.b' β.b e (Equiv.refl _) e).trans (by rw [β.b'b, Matrix.submatrix_one_equiv])
  gl := β.gl.comp (Units.map (Matrix.reindexAlgEquiv k k e).toRingEquiv.toMonoidHom)
  gl_supp g := β.gl_supp _
  gl_mat g := by
    refine (β.gl_mat _).trans ?_
    have h : g.val = (g.val.submatrix e.symm e.symm).submatrix e e := by simp
    conv_rhs => rw [h, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    rfl

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

section Empty

variable {P : Pl D → Prop}

theorem mem_GinfC_of_all (hP : ∀ v, P v) {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) : g ∈ GinfC S := by
  rw [grpOff, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff] at hg
  rw [GinfC, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have e : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h1 : Formalism.L2.Theta.mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P :=
    Ideal.Quotient.eq.1 ((hg i j).trans e.symm)
  have h2 := GlobalTheory.SelfDualAt.eq_zero_of_compFin (finPart D _) fun w => (Submodule.mem_iInf _).1 h1 ⟨w, hP w⟩
  rw [RingHom.map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Empty

end GlobalTheory.FinPl.OffInh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
section
set_option genSizeOfSpec false
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)

structure QLev {v : VCom f.c} {t : W.P.T} (F : GlobalTheory.QPl.QFam v (f.t t)) : Prop where
  places : ∃ pl : Fin F.r ≃ (pk W).Q t, ∀ i, Formalism.L2.NTheta.IsIdemAt (F.Q i).q.e (pl i).1 ∧ (F.Q i).q.v = (pl i).1.under (𝓞 D.host.F)
  mid : ∀ i j d hd, j < D.R.m → ∀ x ∈ KO (F.Q i).k _,
    ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j ∈ levS _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ↔ x ∈ ((F.Q i).T.lev j d hd).J) ∧
    ∀ hx : x ∈ ((F.Q i).T.lev j d hd).J, levChi _ ((pk W).βY j) ((pk W).datYt t j (lvP W))
      ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j) = (((F.Q i).T.lev j d hd).lam ⟨x, hx⟩ : ℂ)
  top : ∀ i, ∀ x ∈ KO (F.Q i).k _, ∀ g, (ofSplit (F.Q i).q).IsLoc (F.Q i).FT g x →
    (f.g.bT⁻¹ * g * f.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ (F.Q i).T.levTop.J)

def VfAt (v : VCom f.c) {t : W.P.T} (w : VTup (f.t t)) (sc : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (f.t t).om j (a * v.b j, a' * v.b (j + 1)) ((f.t t).pt j P) =
    sc j • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ (w.eQ j) (v.Ψ j P a a'))) ∧
  ∀ j h P, (f.t t).omT j h (v.b (j + 1), v.bT) ((f.t t).ptT j h P) =
    sc (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ (w.eQT j h) (v.ΨT j h P))

def GVec (v : VCom f.c) (s : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d → ∀ P, ∀ a ∈ GinfC _,
    ∀ a' ∈ GinfC _, (pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j)
      (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)) =
      s j • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a')) ∧
  ∀ j h d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d → ∀ P,
    omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)) =
      s (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P)

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)

def col0 (t : W.P.T) (φ : D.what₂.Mu u) : (f.t t).Col 0 := D.e0Tw u (W.P.I.tup t) (D.eMu u φ).1

def down (n : ℕ) (h : 2 * n + 2 * 0 + 2 = D.R.m) (t : W.P.T) (F : (f.t t).CT) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h F)).1

def LinkZero (d : BotDat W u) : Prop :=
  ∀ n (h₀ : 0 + 2 * n + 2 = D.R.m) t φ, col0 f t φ ∈ (f.t t).Ram 0 ∧
    ∀ G y v, (f.t t).per 0 n h₀ (col0 f t φ) G y v = d.per φ G.1 y v

def LinkTail : Prop :=
  ∀ n (h : 2 * n = D.R.m) t φ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ G : (f.t t).CT, G.1 = topOf W t F' →
    (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (col0 f t φ)) G =
      D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))

def LinkDown : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m) t (F' : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL),
    ∃ G : (f.t t).CT, G.1 = topOf W t F' ∧ down f n h t G = rowAt W t F'

def LinkOnto : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m), ∀ T ∈ ThetaLiftSpaceZero W, ∃ G : (f.t W.P.A3.A.μ0).CT, down f n h W.P.A3.A.μ0 G = T

def LinkComm : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (s : ℂ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ s ≠ 0 ∧
    ∀ t φ F, (f.t t).tail (2 * n) h ((f.t t).up n (col0 f t φ)) F =
      s * (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (col0 f t (S φ))) F

def RatioOK : Prop :=
  ∀ n, 2 * n = D.R.m → ∀ t, (f.t t).cTop n ≠ 0 ∧
    UnitRatio (fun p => ∃ PP ∈ (pk W).Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ((f.t t).cTop n / (f.t t).cBot)
      ((f.t W.P.A3.A.μ0).cTop n / (f.t W.P.A3.A.μ0).cBot)

variable (W)

def Served : Prop :=
  ∀ w (p : ℕ), p.Prime → (∃ PP ∈ (pk W).Q (W.Q.Rl.mu w), ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal

def FamAll : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (f : FamCh W u) (d : BotDat W u),
    d.Pin z ∧ LawsX f.t ∧ LinkZero f d ∧ LinkTail f ∧ LinkDown f ∧ LinkOnto f ∧ LinkComm f ∧ RatioOK f

open Formalism.L2.Host in

theorem served_holds : Served W := by
  rintro w p hp ⟨PP, hP, h1⟩ h2
  have lev := W.Q.charW.base.lev
  have hr : ¬ (W.Q.Rl.xiH (W.Q.Rl.mu w)).UnrAt PP := (lev.Q_ram _ PP).2 (Or.inl hP)
  have hl : Formalism.EigenvalueLevelCeiling.plc w = p :=
    (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hp).1
      ((ringChar.spec _ p).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2))
  by_cases hw : w ∈ W.Q.Rl.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := W.Q.charW.tup.mu_on w hw
    have e' : W.Q.Rl.xiH (W.Q.Rl.mu w) = W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have key : ∀ q : ℕ, q.Prime → OverP D.host q PP → q = p := fun q hq ho => by
      by_contra hne
      have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have ho' : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := ho
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ ho') (PP.asIdeal.mul_mem_left _ h1)))
    have hd : (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP := by
      unfold CharFrame.delAt
      split_ifs with hh
      · refine W.Q.Rl.C.isDel'.unr PP fun ho => D.host.pde_ne ?_
        rw [← hh, hl, key _ D.host.pde'_prime ho]
      · exact W.Q.Rl.C.isDel.unr PP fun ho => hh (by rw [hl, key _ D.host.pde_prime ho])
    refine hr fun x hx => ?_
    have a1 := hd x hx
    have a2 := hψ.atl PP (hl ▸ h1) x
    rw [e']
    change (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
    rw [a1, a2, mul_one]
  · have e : W.Q.Rl.mu w = W.P.A3.A.μ0 := W.Q.charW.tup.mu_off w hw
    refine hr fun x _ => ?_
    rw [e, show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
    rfl

theorem not_mem_Q_base (PP : HeightOneSpectrum (𝓞 D.host.E)) : PP ∉ (pk W).Q W.P.A3.A.μ0 := by
  intro hP
  have lev := W.Q.charW.base.lev
  refine (lev.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
  rfl

variable {W f}

example : ∃ n, 2 * n = D.R.m := by
  obtain ⟨a, ha⟩ := D.R.m_even
  exact ⟨a, by omega⟩

example : ∃ n, 2 * n + 2 * 0 + 2 = D.R.m ∧ 0 + 2 * n + 2 = D.R.m := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have := D.R.two_le_m
  exact ⟨a - 1, by omega, by omega⟩

example (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) (hp : p.Prime) (hw : (p : 𝓞 D.what₂.LL) ∈ w.asIdeal) :
    ¬ UnitRatio (fun l => ∃ PP ∈ (pk W).Q (W.Q.Rl.mu w), ((l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (p : ℂ) 1 := by
  rintro ⟨-, k, hk, r, -, e, hS⟩
  have hr : r = ((p ^ k : ℕ) : ℚ) := by
    have : (r : ℂ) = (((p ^ k : ℕ) : ℚ) : ℂ) := by rw [← e]; simp
    exact_mod_cast this
  refine served_holds W w p hp (hS p hp ?_) hw
  have := Fact.mk hp
  rw [hr, padicValRat.of_nat, padicValNat.prime_pow]
  exact_mod_cast hk.ne'

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

def realPt (θ : InfFam D) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Classical.epsilon fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ

variable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)

def xiN (f : WO S T → ℂ) (z : VCx D.what₂.Tau a b) : ℂ :=
  Complex.exp ((Real.pi : ℂ) / 2 * HV sc z z) *
    f (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j)))

def toHom (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E) :=
  Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS))

def jetP (s : ℂ) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * jetC (fun _ => s) G (k.mapDomain fun v => (v.1, Fin.cast hT v.2.1, Fin.cast hS v.2.2))

def latFr (V : HSp D) {n : ℕ} (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin V.rank → D.host.E) :=
  {x | (fun i => x (Fin.cast hn.symm i)) ∈ N}

def Moves (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ x : Fin n → D.host.E, x ∈ N ↔ ∀ i, (finM V hn g⁻¹ *ᵥ fun j => eToEAf D (x j)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

structure StdPair (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  sigS : S.SigOK
  sigT : T.SigOK
  rk : 0 < S.rank ∧ S.rank < T.rank ∧ Even S.rank ∧ Even T.rank
  cc : D.host.ccK = ⊤
  ne : δ ≠ 0
  xi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)
  scale : sc * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹

def IsHol (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f

def splitPart (V : HSp D) : Subgroup (GA D V) := Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ SuppAt e V g}

def IsRatFin (V : HSp D) (g : GA D V) : Prop := g ∈ GfC V ∧ ∃ γ ∈ GQ V, finHom V γ = finHom V g

end Gen

section World
variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m)

abbrev ColDat.xiS (f : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ :=
  xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc f

def ColDat.MoveAt (c₀ : ℂ) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (i + 1))) : Prop :=
  ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' →
    ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (A.om i (g, h) (A.vac i)) = fun z =>
        c₀ * (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

def ColDat.VacMove : Prop := ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ g ∈ GfC _, ∀ h ∈ GfC _, A.MoveAt θ i hi c₀ g h

end World

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.StepData GlobalTheory.SymBridge
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

section Gen
variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

def GAt.emb : D.host.E →+* G.k := (ofSplit G.q).π.comp (incA D)

structure GAt.FrTie (fr : ∀ i, i ≤ D.R.m → Matrix (Fin (D.sp.X i).rank) (Fin (D.R.N i)) D.host.E)
    (y : ∀ i, Fin (D.R.N i) → D.host.E) : Prop where
  frX : ∀ i (hi : i ≤ G.s + 1) (hm : i ≤ D.R.m), ∃ e : XIx (Fin D.R.k) (Fin D.R.t) i ≃ Fin (D.R.N i), IsOrd xPos e ∧
    ∀ r a, (G.FX i hi).β r a = G.emb (fr i hm r (e a))
  frM : ∀ hm : G.s + 1 + 1 ≤ D.R.m, ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2) ⊕ Unit ≃ Fin (D.R.N (G.s + 1 + 1)),
    IsOrd (Sum.elim zPos fun _ => D.R.N D.R.m - 1) e ∧ ∀ r a, G.FM.β r a = G.emb (fr (G.s + 1 + 1) hm r (e a))
  coset : ∀ e : XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ≃ Fin (D.R.N (G.s + 1)), IsOrd xPos e → ∀ a,
    G.emb (y (G.s + 1) (e a)) - G.S.y0 (Fin D.R.t) a ∈ 𝒪[G.k]

end Gen

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) {d : Dat (I.rec7 l Z) u}
  {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) (I.rec7 l Z).host.E}

def baseFr (i : ℕ) (hi : i ≤ B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r a =>
  Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P (Pi.single a 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

structure TiedAt {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} (G : GAt d τ PP)
    (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) : Prop where
  eq : P.1 = PP
  type : letI := G.fld; letI := G.val; letI := G.top; letI := G.loc
    AtType (k := G.k) I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) B.embLL P G.emb G.S
  fr : G.FrTie (fun i hi => baseFr A i hi P) fun i =>
    (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P).symm (Formalism.L2.Col.repY (A.p0 i).1.2)

def xiT (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (Formalism.L2.Col.phiT B.fields.K (A.p0 i).1.1.deco.1 (A.p0 (i + 1)).1.1.deco.1
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

def JoinG : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Ch : ℕ → Type)
    (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (A : ColDat I l Z u Ch)
    (d : Dat (I.rec7 l Z) u) τ cG (G : ∀ PP : d.c.Pg, GAt d τ PP.1), I.Ok → I.IsTw → PinColAt d F A → PinGBy G cG →
    d.c.Pg = Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0) → (∀ PP, ∃ P, TiedAt A (G PP) P) →
    ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ i (hi : i + 1 ≤ B.R.m) wT,
      IsRatDatum d.c.ψ _ _ eT (xiT A i hi) (A.vac i) wT → IsThetaFunO d.c.ψ _ _ wT →
      ∃ C : ℂ, C ≠ 0 ∧ A.w i = C • comb d.c.ψ _ _ (cG i) wT

end GlobalTheory.LocMod
end
end


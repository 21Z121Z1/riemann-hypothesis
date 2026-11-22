import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColTOfPinColL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapSpanDenseHeisenbergStableStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingMap_span_dense_heisenbergStable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D), IsStdChar D ψ (-1) → let M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂}; (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧ ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := by
  first | exact @GlobalTheory.Core.Rk.DoubleSpan.main | exact GlobalTheory.Core.Rk.DoubleSpan.main | (intros; apply GlobalTheory.Core.Rk.DoubleSpan.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroNe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest
open GlobalTheory.Fam

section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {a : GeoAll W u}

def cst1 (a : GeoAll W u) : Cst a := ⟨fun _ _ => 1, fun _ => ⟨0, Fin.elim0, Fin.elim0⟩, fun _ _ => 1, fun _ _ => 0, fun _ => 1, fun _ _ => 1⟩

variable {k : Cst a} {row : ∀ t, RowCh (pk W) (lvP W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}
  {w₀ w : ∀ t, VTup ((a.fam row col).t t)} {F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)}

theorem places (h : ColOut k w₀ w F) (t) (p) : p ∈ (w t).Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 D.host.F) := by
  obtain ⟨pl, hp⟩ := (h.lev t).places
  rw [(h.same t).1, (h.pins t).places]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pl i).1, (pl i).2, (hp i).2⟩
  · rintro ⟨PP, hP, rfl⟩
    refine ⟨pl.symm ⟨PP, hP⟩, ?_⟩
    rw [(hp _).2, Equiv.apply_symm_apply]

end Gen

section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True
end GlobalTheory.Fam.ColTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd
open GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

abbrev lineZ (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem gram_X' {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) : (I.rec7 l Z).sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by
    rintro _ n rfl; exact gram_pos hs n
  exact key _ _ h2

def oTop {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) :
    ∀ n, n = (I.rec7 l Z).R.m → OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)) :=
  fun n h => Eq.rec (motive := fun n _ => OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)))
    (topDec (gram_X hI _) (gram_X' hI)) h.symm

def piE (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : (I.rec7 l Z).host.E :=
  ((X.piT u : 𝓞 B.host.E) : B.host.E)

def zeta (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : Fin (lineZ (I.rec7 l Z)).rank → (I.rec7 l Z).host.E :=
  fun _ => piE I l Z u

def xgeo {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok)
    (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (u : B.Word)
    (Λ : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : XGeo (I.rec7 l Z) :=
  ⟨fun _ => stdSp _, vac, lineZ _, oTop l Z hI, zeta I l Z u, 1, Λ⟩

theorem norm_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    star (zeta I l Z u) ⬝ᵥ (lineZ (I.rec7 l Z)).gram *ᵥ zeta I l Z u = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) := by
  have h := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (l.pr.piT_norm u)
  rw [gram_pos, Matrix.one_mulVec]
  simp only [dotProduct, zeta, piE, Pi.star_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_mul, map_natCast] at h
  rw [show (lineZ (I.rec7 l Z)).rank = 1 from rfl, one_smul]
  exact (mul_comm _ _).trans h

theorem isLineVec_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    IsLineVec (lineZ (I.rec7 l Z)) (zeta I l Z u) := by
  refine ⟨rfl, ?_⟩
  rw [norm_zeta]
  have := (l.pr.T_prime u).ne_zero
  exact_mod_cast this

theorem eq_latFrame_of_isSDFrame {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.PlaceModel.latFrame V := by
  obtain ⟨c, -, -, -, h4, h5⟩ := h
  ext x
  constructor
  · intro hx
    have := h5 x hx
    rw [one_pow, Nat.cast_one, one_smul] at this
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame]
    exact this
  · intro hx
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame] at hx
    have := h4 x hx
    rwa [one_pow, Nat.cast_one, one_smul] at this

end GlobalTheory.XGeoStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.SplitIntComp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

theorem eq_sec_add_csec (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  have h := (idem_iff q a).1 ha
  rw [q.sec_pr, q.sec_pr, map_mul, cA_cA]
  conv_lhs => rw [← h]
  ring

theorem mem_intAt_iff (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨(q.int_iff _).2 ?_, (q.int_iff _).2 ?_⟩
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 h.2
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 ((cA_int_iff a).2 h.2)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [eq_sec_add_csec q ha, RingHom.map_add]
    exact add_mem ((q.int_iff _).1 h1) ((cA_int_iff _).2 ((q.int_iff _).1 h2))

theorem val_xi (q : SplitPt D k) (h : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have he := e_mem_intAt q
  have hpe : q.pr q.e = 1 := by rw [← sec_one q, q.pr_sec]
  have h1 := ((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1
  have h2 := ((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1
  rw [map_mul, hpe, mul_one] at h1 h2
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 := congrArg (valuation k) hprod
  rw [map_mul, map_one] at v3
  refine le_antisymm v1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one
  rw [v3, mul_one] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitIntComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevPin
open GlobalTheory.FinPl (idAt MxAt grpAt SplitPt)

variable {D : D7}

theorem idAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, P w → P' w) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mxAt_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {m n : ℕ} (w : Mx D m n)
    (h : IsHalf (q.e + cA D q.e) w) : MxAt P w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  refine idAt_mono (fun w (hw : w = q.v) => hw ▸ hP) (GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_)
  rw [← h2]
  exact h i j

theorem exists_fold (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) {ι : Type} (c : ι → WO S T →₀ ℂ)
    (hc : ∀ i, ∀ w ∈ (c i).support, MxAt P w) (l : List ι) : ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, MxAt P w) ∧
      ∀ f, comb ψ S T c' f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun w hw => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hw)
      exact fun i j => zero_mem _
    · rw [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul,
        GlobalTheory.MixPer.heisO_zero]
      rfl
  | cons i l ih =>
    obtain ⟨c', h1, h2⟩ := ih
    obtain ⟨c'', h3, h4⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c i) c'
    refine ⟨c'', fun w hw => ?_, fun f => by rw [h4, h2]; rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h3 w hw
    exact fun a b => add_mem (hc i x hx a b) (h1 y hy a b)

theorem mxAt_cast {F : ℕ → HSp D} {T : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {s j : ℕ} (h : s = j) (x : WO (F s) T →₀ ℂ)
    (hx : ∀ w ∈ x.support, MxAt P w) : ∀ w ∈ (cast (congrArg (fun n => WO (F n) T →₀ ℂ) h) x).support, MxAt P w := by
  subst h
  exact hx

def conjHom {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) :
    GL (Fin N) k →* GL Y k where
  toFun g := ⟨F.γ * g.val * F.β, F.γ * (g⁻¹).val * F.β, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc g.val,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, F.γβ], by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc (g⁻¹).val,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (1 : Matrix (Fin N) (Fin N) k) * F.β = 1
    rw [Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (g.val * h.val) * F.β = (F.γ * g.val * F.β) * (F.γ * h.val * F.β)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul])

theorem conj_iff {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y)
    (M : GL (Fin N) k) (x : GL Y k) : M.val = F.β * x.val * F.γ ↔ x = conjHom F M := by
  constructor
  · intro h
    refine Units.ext ?_
    change x.val = F.γ * M.val * F.β
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  · rintro rfl
    change M.val = F.β * (F.γ * M.val * F.β) * F.γ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) : Subgroup G :=
  J.comap ((conjHom F).comp ρ)

theorem mem_frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) (g : G) :
    g ∈ frameSub ρ F J ↔ ∀ x : GL Y k, (ρ g).val = F.β * x.val * F.γ → x ∈ J := by
  constructor
  · intro h x hx
    rw [(conj_iff F _ x).1 hx]
    exact h
  · intro h
    exact h _ ((conj_iff F _ _).2 rfl)

theorem under_inj {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hT : GlobalTheory.Core.Mi.IsTypePlaces Pg) {PP PP' : Formalism.L2.DIV.Pl D.host.E}
    (h : PP ∈ Pg) (h' : PP' ∈ Pg) (e : PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F)) : PP = PP' := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    have := hT.1 PP h
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using this
  obtain ⟨Q, _, hu⟩ := hT.2 _ hm
  exact (hu PP ⟨h, rfl⟩).trans (hu PP' ⟨h', e.symm⟩).symm

end GlobalTheory.LevPin

namespace GlobalTheory.LevPin

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_locComb {a : XGeo D} {y : YRat a} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) {N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)} {β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)}
    {b : ∀ j, GA D (Yc D j)} {bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k}
    (Y : LocY l y N β b bas) (ν : Measure l.k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (eg : ∀ j, WO (Yc D j) (Yc D (j + 1)) →₀ ℂ) (egT : WO (Yc D (l.s + 1)) D.sp.X' →₀ ℂ)
      (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ),
      (∀ j a' (H : j + a' = l.s), (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) (eg j)
        ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      (ofSplit l.q).IsCombAt ψ (Y.FY (l.s + 1) 0 rfl) l.FT egT (S.T (Fin D.R.t)).PhiTop ∧
      (∀ j a' (H : j + 1 + a' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) (cg j)
        ((S.T (Fin D.R.t)).entry S.ψ ν j a' H 1 1)) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl) (cg l.s)
        (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX (l.s + 1) le_rfl) l.FM (cg (l.s + 1))
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) ∧
      (∀ j, ∀ w ∈ (eg j).support, IsHalf (l.q.e + cA D l.q.e) w) ∧ (∀ j, ∀ w ∈ (cg j).support, IsHalf (l.q.e + cA D l.q.e) w) := by
  have keyE : ∀ j, ∃ c : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ a' (H : j + a' = l.s),
      (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) c ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j ≤ l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY j (l.s - j + 1) (by omega))
        (Y.FY (j + 1) (l.s - j) (by omega)) ((S.T (Fin D.R.t)).Phi j (l.s - j) (by omega))
      refine ⟨c, fun a' H => ?_, hc.1⟩
      obtain rfl : a' = l.s - j := by omega
      exact hc
    · exact ⟨0, fun a' H => by omega, by simp⟩
  choose eg heg sEg using keyE
  obtain ⟨egT, hegT⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY (l.s + 1) 0 rfl) l.FT
    (S.T (Fin D.R.t)).PhiTop
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX (l.s + 1) le_rfl) l.FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have keyC : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = l.s → HEq c c₁) ∧ (j = l.s + 1 → HEq c c₂) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j < l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX j (by omega)) (l.FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j (l.s - j - 1) (by omega) 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega, hc.1⟩
      obtain rfl : c'' = l.s - j - 1 := by omega
      exact hc
    · by_cases h1 : j = l.s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega, h₁.1⟩
      · by_cases h2 : j = l.s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl, h₂.1⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim, by simp⟩
  choose cg k1 k2 k3 k4 using keyC
  refine ⟨eg, egT, cg, heg, hegT, k1, ?_, ?_, sEg, k4⟩
  · rw [eq_of_heq (k2 l.s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (l.s + 1) rfl)]; exact h₂

end GlobalTheory.LevPin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroMoveConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.VacBase

theorem vacuum_reads_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ c₀ : ℂ, c₀ ≠ 0 ∧ A.MoveAt θ i hi c₀ 1 1 := by
  intro B X I l Z w u A ψ θ hA i hi
  obtain ⟨hstd, -, -, -⟩ := GlobalTheory.T.standard_pair_along_chain I l Z w u A ψ θ hA i hi
  have key := GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi)
    I.A.δ I.A.sc hstd (A.chr (i + 1)) (A.om i) (hA.om i hi) (A.vac i) (hA.vac i hi) 1 (one_mem _) 1 (one_mem _)
  have S1 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := GlobalTheory.T.adelicTranslate_one_eq_standardLattice
  have S2 : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ),
      IsDetRoot V 1 x → μ x = 1 := GlobalTheory.T.character_eq_one_of_isDetRoot_of_even
  have S3 : ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
        (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))),
      ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i))
        (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := GlobalTheory.T.lattice_chain_standard_pair I l Z w i hi
  by_cases hex : Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) ∧
      Moves _ (rankN (I.rec7 l Z) (i + 1) hi) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))
  · obtain ⟨-, hmem, hne⟩ := key _ _ hex.1 hex.2
    obtain ⟨c, hc⟩ := S3 _ hmem
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      apply hne
      exact hc.trans (zero_smul _ _)
    · intro N N' hN hN' x y hx hy
      obtain rfl := S1 _ _ _ _ N hN
      obtain rfl := S1 _ _ _ _ N' hN'
      have hx1 : A.chr (i + 1) x = 1 := S2 _ _ _ (hA.om i hi).resS hstd.rk.2.2.1 _ x hx
      have hy1 : A.chr (i + 1) y = 1 := S2 _ _ _ (hA.om i hi).resT hstd.rk.2.2.2 _ y hy
      rw [hx1, hy1]
      show xiN θ _ _ _ _ I.A.δ I.A.sc _ = _
      refine hc.trans ?_
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, Circle.coe_one, inv_one, mul_one]
      rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    intro N N' hN hN'
    exact absurd ⟨S1 _ _ _ _ N hN ▸ hN, S1 _ _ _ _ N' hN' ▸ hN'⟩ hex

end GlobalTheory.AdForm.VacBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRedIffIsPat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem exists_red_iff_isPat : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP), (∃ x, GlobalTheory.LevZero.Red G PP x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D c v G PP hidem g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hidem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := GlobalTheory.SymRes.exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.LevZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardCartanInvolution_commute_compact : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  first | exact @GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K | exact GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K | (intros; apply GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K <;> assumption)
end


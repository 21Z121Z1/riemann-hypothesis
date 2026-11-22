import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnitPairEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReindexIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AconvSingleList
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep.IdempotentCombination

variable {D : D7}

section Idem
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_idem (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, -, h4⟩ := q.above
  rw [h4]
  show cA D (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = ε ⊗ₜ[D.host.F] (1 : D.host.E)
  simp [cA, sigR]

theorem idem_sq (q : GlobalTheory.FinPl.SplitPt D k) : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  have h1 := q.split.1
  have h2 := q.split.2.1
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  linear_combination h1 + 2 * h2 + h3

end Idem

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (e :: l) = ∑ g ∈ e.support, ∑ h ∈ (aconv l).support, Finsupp.single (g + h) (e g * aconv l h) := rfl

theorem comb_aconv_cons (e : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, aconv_cons]
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0, AddChar.map_zero_eq_one,
    one_smul]

end GlobalTheory.TriStep.IdempotentCombination

namespace GlobalTheory.TriStep

theorem aconv_single_list {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  show d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b)) = d
  calc d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b))
        = d.sum (fun g a => Finsupp.single g a) := by
          congr 1; funext g a; rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
    _ = d := Finsupp.sum_single d

theorem comb_aconv_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {A T : HSp D}
    (c d : WO A T →₀ ℂ) (hc : Q.Away c)
    (hd : ∀ u ∈ d.support, IsHalf ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) u) (g : WO A T → ℂ) :
    comb ψ A T (aconv [c, d]) g = comb ψ A T c (comb ψ A T d g) := by
  rw [GlobalTheory.TriStep.IdempotentCombination.comb_aconv_cons c [d] ?_ g, aconv_single_list]
  intro x hx y hy
  rw [aconv_single_list] at hy
  have hy' : IsHalf (Q.q.e + cA D Q.q.e) y := hd y hy
  refine GlobalTheory.HeisComb.symplO_half A T (1 - (Q.q.e + cA D Q.q.e)) (Q.q.e + cA D Q.q.e) x y ?_ ?_ (hc x hx) hy'
  · rw [map_sub, map_one, GlobalTheory.TriStep.IdempotentCombination.cA_idem]
  · rw [sub_mul, one_mul, GlobalTheory.TriStep.IdempotentCombination.idem_sq, sub_self]

theorem valK_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hcon Ξ₁ Ξ₂ d₁ d₂ hd₁ hd₂ O₁ O₂ hO₁ hO₂ f hf
  have hσc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol
  let P₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let P₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₁ : SB (Matrix Q.n₁ Q.n₀ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₂ : SB (Matrix Q.n₂ Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have e₁ : flatBF S.s₁ (T₁ O₁) = U₁ P₁ := hU₁ O₁ P₁ (by
    rw [hO₁, (hun Q.n₁ Q.n₀ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)])
  have e₂ : flatFB S.s₂ (T₂ O₂) = U₂ P₂ := hU₂ O₂ P₂ (by
    rw [hO₂, (hun Q.n₂ Q.n₁ Q.n₀ (Q.c + 1) (σ + 1)).2.1 (by omega) (by omega)])
  obtain ⟨ΞO, hΞO, eΛ⟩ := hcon P₁ P₂
  have hΞO' : ∀ q, ΞO.1 q = R₁.1 q.1 * R₂.1 q.2 := fun q => by
    rw [hΞO]; exact (hun Q.n₁ Q.n₀ Q.n₂ 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) ψ Q.n₁ Q.n₀ Q.n₂).1 S.B.A S.J.W₀ S.B'.A
    Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ d₁ d₂ Ξ₁ R₁ Ξ₂ R₂ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) ΞO hΛ hd₁ hd₂ rfl rfl (fun q => rfl) hΞO'
  have hbc := GlobalTheory.ProdLocInv.biComb_comp ψ S.B.A S.J.W₀ S.B'.A c₁ d₁ (aconv [c₁, d₁]) c₂ d₂ (aconv [c₂, d₂])
    (comb_aconv_away Q c₁ d₁ hc₁ hd₁.1) (comb_aconv_away Q c₂ d₂ hc₂ hd₂.1) (Λ ΞO)
  have hom₁ : S.s₁.om (1, 1) = 1 := map_one _
  have hom₂ : S.s₂.om (1, 1) = 1 := map_one _
  simp only [GlobalTheory.TriStep.valK, Dbl2.val, Dbl2.con, GlobalTheory.TriStep.rTrans_one]
  rw [hom₁, hom₂, Module.End.one_apply, Module.End.one_apply, e₁, e₂, eΛ, ← hbc, hbi]

end GlobalTheory.TriStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_conductor_integers_continuous_ne_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle),
    HasConductor ψ 1 → Continuous ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.hasConductor_one_continuous_ne_one | exact GlobalTheory.hasConductor_one_continuous_ne_one | (intros; apply GlobalTheory.hasConductor_one_continuous_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicSchwartzSlicePolynomialGaussianOfAnnihilatStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_slice_polynomial_gaussian_of_annihilated : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ), ∀ φ ∈ schwartzA θ V.rank n, (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0) → ∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) := by
  first | exact @GlobalTheory.StdUnn.Slice.slice_polyGauss | exact GlobalTheory.StdUnn.Slice.slice_polyGauss | (intros; apply GlobalTheory.StdUnn.Slice.slice_polyGauss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AtOneInt
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open GlobalTheory.FinPl (SplitPt grpAt grpOff)
open GlobalTheory.SymCompare (sE)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes (places IsUnitPair put biPut volK IsCptOpen RowComb)

namespace GlobalTheory.QCmp

section Many
variable {D : D7} {I : Type} [Fintype I] [DecidableEq I] {k : I → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
  [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
variable {Y Y' : I → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] [∀ i, Fintype (Y' i)] [∀ i, DecidableEq (Y' i)]

def Emb (q : ∀ i, SplitPt D (k i)) (V : HSp D) (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i))
    (ι : (∀ i, GL (Y i) (k i)) → GA D V) : Prop :=
  ∀ x, ι x ∈ grpAt V (places q) ∧ ∀ i, (mt V (ι x)).map (q i).pr = (F i).β * (x i).val * (F i).γ

def intP {V : HSp D} (ι : (∀ i, GL (Y i) (k i)) → GA D V) : Set (GA D V) := {h | ∃ x, (∀ i, x i ∈ KO (k i) (Y i)) ∧ ι x = h}

def prodC {V : HSp D} (ι : (∀ i, GL (Y i) (k i)) → GA D V) (e : ∀ i, GL (Y i) (k i) →₀ ℂ) (h : ∀ i, GL (Y i) (k i)) :
    GA D V →₀ ℂ :=
  ∑ g ∈ Fintype.piFinset fun i => (e i).support, Finsupp.single (ι (g * h)) (∏ i, e i (g i))

def Vacs (q : ∀ i, SplitPt D (k i)) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}
    (FS : ∀ i, GlobalTheory.LocMod.Frame (k i) S.rank (Y' i)) (FT : ∀ i, GlobalTheory.LocMod.Frame (k i) T.rank (Y i)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ i, ∃ Tm, (ofSplit (q i)).IsModel ψ (FS i) (FT i) Tm ∧ ∀ O, IsOne O → Tm O = f

end Many

def AtOneIdx (D : D7) (I : Type) [Fintype I] [DecidableEq I] (n₀ n₁ n₂ : I → Type) [∀ i, Fintype (n₀ i)]
    [∀ i, DecidableEq (n₀ i)] [∀ i, Fintype (n₁ i)] [∀ i, DecidableEq (n₁ i)] [∀ i, Fintype (n₂ i)] [∀ i, DecidableEq (n₂ i)]
    (c : I → ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (χ₁ χ₂ χz : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omb : Om J.W₀ B'.A),
    s₁.χV = χ₁ * χz → s₁.χW = χ₁ → s₂.χV = χ₂ → s₂.χW = χ₂ * χz →
    IsWeilDatumO ψ B.A J.W₀ χ₁ χ₁ oma → IsWeilDatumO ψ J.W₀ B'.A χ₂ χ₂ omb →

  ∀ (k : I → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] [∀ i, MeasurableSpace (k i)] [∀ i, BorelSpace (k i)]
    (q : ∀ i, SplitPt D (k i)), (Function.Injective fun i => (q i).v) →
  ∀ (ψk : ∀ i, AddChar (k i) Circle) (ν : ∀ i, Measure (k i)) (μ₁ μ₂ : ∀ i, (k i)ˣ →* ℂˣ),
    (∀ i, (ofSplit (q i)).IsChar ψ (ψk i) ∧ HasConductor (ψk i) 1 ∧ IsUnitVol (ν i) ∧
      (ofSplit (q i)).IsComp χ₁⁻¹ (μ₁ i) ∧ (ofSplit (q i)).IsComp χ₂⁻¹ (μ₂ i)) →

  ∀ (F : ∀ i, Dbl (ofSplit (q i)) B J B' (n₀ i) (n₁ i) (n₂ i) (c i))
    (ι₀ : (∀ i, GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)) → GA D B.V) (ι₁ : (∀ i, GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i)) → GA D J.W)
    (ι₂ : (∀ i, GL (n₂ i ⊕ Fin (c i + 1)) (k i)) → GA D B'.V),
    Emb q B.V (fun i => (F i).G₀) ι₀ → Emb q J.W (fun i => (F i).G₁) ι₁ → Emb q B'.V (fun i => (F i).G₂) ι₂ →
  ∀ (m₁ : Measure (grpAt J.W (places q))) (ρ₁ : Measure ((jacGrp J.d).subgroupOf (grpAt J.W (places q))))
    (m₂ : Measure (grpAt B'.V (places q))) (ρ₂ : Measure ((besGrp B'.d B'.o).subgroupOf (grpAt B'.V (places q)))),
    IsUnitPair _ (jacGrp J.d) (intP ι₁) ρ₁ m₁ → IsUnitPair _ (besGrp B'.d B'.o) (intP ι₂) ρ₂ m₂ →

  ∀ (P₀ : ∀ i, GlobalTheory.StepData.Level (GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)))
    (P₁ : ∀ i, GlobalTheory.StepData.Level (GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i)))
    (P₂ : ∀ i, GlobalTheory.StepData.Level (GL (n₂ i ⊕ Fin (c i + 1)) (k i)))
    (Φ₁ : ∀ i, SB (Matrix (n₁ i ⊕ Fin (c i + 1 + 1)) (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)))
    (Φ₂ : ∀ i, SB (Matrix (n₂ i ⊕ Fin (c i + 1)) (n₁ i ⊕ Fin (c i + 1 + 1)) (k i))),
    (∀ i, ((P₁ i).J ≤ KO (k i) _ ∧ (P₂ i).J ≤ KO (k i) _) ∧ IsCptOpen (P₁ i).J ∧ IsCptOpen (P₂ i).J ∧
      GlobalTheory.StepData.HasTypes (μ₁ i) (P₀ i) (P₁ i) (Φ₁ i).1 ∧
      GlobalTheory.StepData.HasTypes (μ₂ i) (P₁ i) (P₂ i) (Φ₂ i).1) →
  ∀ (f₁ : WO B.V J.W → ℂ) (f₂ : WO J.W B'.V → ℂ) (d₁ : I → WO B.V J.W →₀ ℂ) (d₂ : I → WO J.W B'.V →₀ ℂ),
    Vacs q ψ (fun i => (F i).G₀) (fun i => (F i).G₁) f₁ → Vacs q ψ (fun i => (F i).G₁) (fun i => (F i).G₂) f₂ →
    (∀ i, (ofSplit (q i)).IsCombAt ψ (F i).G₀ (F i).G₁ (d₁ i) (Φ₁ i).1 ∧
      (ofSplit (q i)).IsCombAt ψ (F i).G₁ (F i).G₂ (d₂ i) (Φ₂ i).1) →

  ∀ (a : ∀ i, GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i)) (e₀ : ∀ i, GL (n₀ i ⊕ Fin (c i + 1 + 1 + 1)) (k i) →₀ ℂ),
    (∀ i, RowComb (ψk i) (ν i) (σ + 2) (P₀ i) (a i) (e₀ i)) →

  ∀ (T₁ : ∀ i, Finset (GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i))) (T₂ : ∀ i, Finset (GL (n₂ i ⊕ Fin (c i + 1)) (k i))),
    (∀ i, GlobalTheory.PosOne.Covers 1 (P₁ i).J (T₁ i) (GlobalTheory.StepData.flat (ψk i) (ν i) (μ₁ i) (Φ₁ i).1 (a i)) ∧
      ∀ β ∈ T₁ i, GlobalTheory.PosOne.Covers 1 (P₂ i).J (T₂ i) (GlobalTheory.StepData.flat (ψk i) (ν i) (μ₂ i) (Φ₂ i).1 β)) →

  ∀ (x₁ : ∀ i, GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i) → WO B.A J.W₀ →₀ ℂ)
    (x₂ : ∀ i, GL (n₁ i ⊕ Fin (c i + 1 + 1)) (k i) → GL (n₂ i ⊕ Fin (c i + 1)) (k i) → WO J.W₀ B'.A →₀ ℂ)
    (e₂ : ∀ i, GL (n₂ i ⊕ Fin (c i + 1)) (k i) → GL (n₂ i ⊕ Fin (c i + 1)) (k i) →₀ ℂ),
    (∀ i, ∀ β ∈ T₁ i, (ofSplit (q i)).IsCombAt ψ (F i).F₀ (F i).F₁ (x₁ i β)
      (GlobalTheory.StepData.xi (ψk i) (ν i) (μ₁ i) (Φ₁ i).1 (P₁ i).J 1 (a i) β)) →
    (∀ i, ∀ β ∈ T₁ i, ∀ γ ∈ T₂ i, (ofSplit (q i)).IsCombAt ψ (F i).F₁ (F i).F₂ (x₂ i β γ)
      (GlobalTheory.StepData.xi (ψk i) (ν i) (μ₂ i) (Φ₂ i).1 (P₂ i).J 1 β γ)) →
    (∀ i, ∀ γ ∈ T₂ i, RowComb (ψk i) (ν i) (σ + 1) (P₂ i) γ (e₂ i γ)) →

  ∀ (φ : GA D B.A → ℂ) (f : GA D B'.V → ℂ), IsContAut B.A φ → IsContAut B'.V f →
    (∀ x : ∀ i, (P₂ i).J, rTrans (ι₂ fun i => (x i).1) f = (∏ i, ((P₂ i).lam (x i) : ℂ)) • f) →
    Iter2 ρ₁ m₁ ρ₂ m₂
      (fun h₁ h₂ => (prodC ι₀ e₀ a).sum fun g w => w *
        B'.per ψ (biLift oma omb B.vA J.v0 φ (GlobalTheory.Unf.contr l J.W₀ vL
          (flatBF s₁ (s₁.om (g, h₁.1) (put ψ d₁ f₁))) (flatFB s₂ (s₂.om (h₁.1, h₂.1) (put ψ d₂ f₂))))) (rTrans h₂.1 f))
      ((∏ i, ((volK (P₁ i).J * volK (P₂ i).J : ℝ) : ℂ)) *
        ∑ β ∈ Fintype.piFinset T₁, ∑ γ ∈ Fintype.piFinset T₂,
          (∏ i, (((volK (GlobalTheory.StepData.prX (GlobalTheory.StepData.Cgrp (P₁ i).J (β i))))⁻¹ *
            (volK (GlobalTheory.StepData.prX (GlobalTheory.StepData.Cgrp (P₂ i).J (γ i))))⁻¹ : ℝ) : ℂ)) *
          B'.per ψ (biLift oma omb B.vA J.v0 φ (biPut ψ (fun i => x₁ i (β i)) (fun i => x₂ i (β i) (γ i))
              (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ f₁) (flatFB s₂ f₂))))
            (trc (prodC ι₂ (fun i => e₂ i (γ i)) γ) f))

def AtOneInt (D : D7) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (c : ℕ), AtOneIdx D I (fun _ => n₀) (fun _ => n₁) (fun _ => n₂) fun _ => c

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def BaseAt {r : ℕ} (Q : Fin r → QStep S) : Prop :=
  ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ v, P v ↔ ∃ i, (Q i).q.v = v) →
  ∀ (μ₁ : Measure (grpAt S.J.W P)) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W P)))
    (μ₂ : Measure (grpAt S.B'.V P)) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V P))),
    μ₁.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₂.IsHaarMeasure → ρ₂.IsHaarMeasure →
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 → ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 →
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 → ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1 →
  ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → (∀ i, (Q i).Vac f₁ f₂) →
  ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → (∀ i, (Q i).Typed f) →
    Iter2 ρ₁ μ₁ ρ₂ μ₂
      (fun x y => GlobalTheory.QVal.integrand Q (Finsupp.single 0 1) (Finsupp.single 0 1) f₁ f₂ φ f 1 1 1 x.1 y.1)
      (GlobalTheory.QVal.value Q (Finsupp.single 0 1) (Finsupp.single 0 1) f₁ f₂ φ f 1 1 1)

def Same (Q Q' : QStep S) : Prop :=
  Q'.q.v = Q.q.v ∧ (∀ x, IntAt Q'.q.v Q'.gl₁ x ↔ IntAt Q.q.v Q.gl₁ x) ∧ (∀ x, IntAt Q'.q.v Q'.gl₂ x ↔ IntAt Q.q.v Q.gl₂ x) ∧
    Q'.D₁ = Q.D₁ ∧ Q'.D₂ = Q.D₂ ∧ Q'.e₀.mapDomain Q'.gl₀ = Q.e₀.mapDomain Q.gl₀ ∧ Q'.volJ = Q.volJ ∧
    (∀ f₁ f₂, Q.Vac f₁ f₂ → Q'.Vac f₁ f₂) ∧ (∀ f, Q.Typed f → Q'.Typed f) ∧
    ∃ (a : Q.A₁ ≃ Q'.A₁) (b : Q.A₂ ≃ Q'.A₂), (∀ γ, Q'.w₁ (a γ) = Q.w₁ γ ∧ Q'.d₁ (a γ) = Q.d₁ γ) ∧
      (∀ β, Q'.w₂ (b β) = Q.w₂ β ∧ (Q'.e₂ (b β)).mapDomain Q'.gl₂ = (Q.e₂ β).mapDomain Q.gl₂) ∧
      ∀ γ β, Q'.d₂ (a γ) (b β) = Q.d₂ γ β

theorem Same.refl (Q : QStep S) : Same Q Q :=
  ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, fun _ h => h, Equiv.refl _, Equiv.refl _,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

def reFrame {k : Type} [Field k] {N : ℕ} {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (F : GlobalTheory.LocMod.Frame k N Y) (e : Y ≃ Z) : GlobalTheory.LocMod.Frame k N Z where
  β := F.β.submatrix id e.symm
  γ := F.γ.submatrix e.symm id
  βγ := by rw [submatrix_mul_equiv, F.βγ, submatrix_id_id]
  γβ := by
    rw [show F.γ.submatrix e.symm id * F.β.submatrix id e.symm = (F.γ * F.β).submatrix e.symm e.symm from
      submatrix_mul_equiv _ _ _ (Equiv.refl _) _, F.γβ, submatrix_one_equiv]

end GlobalTheory.QCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaAdjointTauFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem doubleSum_eq_dotProduct_mapMatrix_mulVec {R K : Type*} [CommRing R] {m n : ℕ} (g : R → R) (f : K → R)
    (s : Fin m → R) (G : Matrix (Fin m) (Fin n) K) (v : Fin n → R) :
    (∑ i, ∑ j, g (s i) * f (G i j) * v j) = (fun i => g (s i)) ⬝ᵥ (G.map f *ᵥ v) := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem ringHom_conjTranspose_smul_dotProduct_adjoint {R : Type*} [CommRing R] {m n : ℕ} (σ : R →+* R) (c : R)
    (s : Fin m → R) (Y : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (a : Fin n → R) :
    (fun i => σ (s i)) ⬝ᵥ ((c • ((Y.map σ)ᵀ * G)) *ᵥ a)
      = c * ((fun k => σ ((Y *ᵥ s) k)) ⬝ᵥ (G *ᵥ a)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 2
  funext k
  simp [vecMul, mulVec, dotProduct, map_sum, map_mul, mul_comm]

set_option maxHeartbeats 2000000 in

theorem kappa_adj : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  intro D ρ B L' ζ' l S x a s
  simp only [Link.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  have hG : gA S * giA S = 1 := by
    have h := Matrix.mul_nonsing_inv (HSpace.gram S) (gram_isUnit_det S)
    have h2 : (HSpace.gram S * (HSpace.gram S)⁻¹).map (incA D)
        = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) := by rw [h]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  rw [doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D) s, doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D)]
  rw [show (HSpace.gram S).map (incA D) = gA S from rfl,
    show (HSpace.gram B.L).map (incA D) = gA B.L from rfl]
  have hG' : ∀ N : Mx D S.rank B.L.rank, HMul.hMul (gA S) (HMul.hMul (giA S) N) = N := by
    intro N
    rw [← Matrix.mul_assoc, hG]
    exact Matrix.one_mul N
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, hG']
  exact ringHom_conjTranspose_smul_dotProduct_adjoint (cA D) _ s _ _ a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

set_option maxHeartbeats 1000000 in
theorem contr_comb_main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) ∧ (∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ), contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) = biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂)) ∧ ∀ (P : Pl D → Prop) (LA : Lat B.A) (LS : Lat S) (LA' : Lat B'.A) (M : Lat B.V₀) (M' : Lat B'.V₀), IsSelfDualC B.A LA → IsSelfDualC S LS → IsSelfDualC B'.A LA' → IsSelfDualC B.V₀ M → IsSelfDualC B'.V₀ M' → (∀ v, P v → (∃ LL, OrthAt B.o M LA LL v) ∧ ∃ LL, OrthAt B'.o M' LA' LL v) → Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → BiVacAt ψ LA LS LA' P (contr l S vL f₁ f₂) := by
  intro D ψ _ ρ σ B B' l S vL f₁ f₂ h₁ h₂
  obtain ⟨hc, hp⟩ := GlobalTheory.T.theta_contraction_integrand_continuous_periodic D ρ σ B B' l S ψ f₁ f₂ h₁ h₂
  have pc := GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
    (fun w p => f₂ ((B'.o.resT S).symm (p.2, w)) * f₁ ((B.o.resS S).symm (p.1, l.κ S w))) hc
    (fun γ hγ w p => hp γ hγ w p.1 p.2)
  have hint : ∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn
      (fun w => f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ :=
    fun u v => pc.1 (u, v)
  have hcont : Continuous fun p : WO B.A S × WO S B'.A => contr l S vL f₁ f₂ p.1 p.2 := pc.2.1
  obtain ⟨hqL, hqR⟩ := GlobalTheory.T.theta_contraction_quasi_periodic_rational D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  have hsm := GlobalTheory.T.theta_contraction_isBiSmooth D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  have hBi : IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) := {
    cont := hcont
    smooth := hsm
    quasiL := hqL
    quasiR := hqR
    levL := by
      obtain ⟨U, hU, hUf⟩ := h₁.level
      refine ⟨U.comap (extL (S := S) B.o), hU.preimage (continuous_extL B.o), fun a ha hai v => ?_⟩
      funext u
      rw [heis_left, ← extL_apply, hUf _ ha (extL_inf B.o a hai)]
    levR := by
      obtain ⟨U, hU, hUf⟩ := h₂.level
      refine ⟨U.comap (extR (S := S) B'.o), hU.preimage (continuous_extR B'.o), fun a ha hai u => ?_⟩
      funext v
      rw [heis_right, ← extR_apply, hUf _ ha (extR_inf B'.o a hai)] }
  refine ⟨hBi, GlobalTheory.T.theta_contraction_extendByZero_double_combination D ρ σ B B' l S vL ψ f₁ f₂ hint, ?_⟩
  intro P LA LS LA' M M' hLA hLS hLA' hM hM' hor hv₁ hv₂
  have hor1 : ∀ v, P v → ∃ LL, OrthAt B.o M LA LL v := fun v hv => (hor v hv).1
  have hor2 : ∀ v, P v → ∃ LL, OrthAt B'.o M' LA' LL v := fun v hv => (hor v hv).2
  have memL : ∀ a ∈ latO B.A S (LA : Set _) (LS : Set _) P, extL (S := S) B.o a ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    fun a ha => GlobalTheory.T.extendByZero_left_mem_core_lattice D B.V₀ B.A B.L S B.o P LA LS M hLA hLS hM hor1 a ha
  have memR : ∀ b ∈ latO S B'.A (LS : Set _) (LA' : Set _) P, extR (S := S) B'.o b ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P :=
    fun b hb => GlobalTheory.T.extendByZero_right_mem_core_lattice D B'.V₀ B'.A B'.L S B'.o P LA' LS M' hLA' hLS hM' hor2 b hb
  refine ⟨fun v => ⟨?_, ?_, ?_⟩, fun u => ⟨?_, ?_, ?_⟩⟩
  · exact {
      quasi := fun γ u => hqL γ u v
      level := by
        obtain ⟨U, hU, h⟩ := hBi.levL
        exact ⟨U, hU, fun a ha hai => h a ha hai v⟩
      cont := by
        have hh : Continuous fun u : WO B.A S => ((u, v) : WO B.A S × WO S B'.A) := continuous_id.prodMk continuous_const
        exact hcont.comp hh
      smooth := fun k L hL hLf w => by
        have := hsm k L 0 hL continuous_zero hLf (fun _ => by simp) w v
        simpa using this }
  · intro a ha
    funext u
    rw [heis_left, ← extL_apply, map_nsmul, hv₁.2.1 _ (memL a ha)]
  · intro e he a ha hh
    funext u
    rw [heis_left, ← extL_apply, hv₁.2.2 e he _ (memL a ha) (extL_half B.o e a hh)]
  · exact {
      quasi := fun γ v => hqR γ u v
      level := by
        obtain ⟨U, hU, h⟩ := hBi.levR
        exact ⟨U, hU, fun a ha hai => h a ha hai u⟩
      cont := by
        have hh : Continuous fun v : WO S B'.A => ((u, v) : WO B.A S × WO S B'.A) := continuous_const.prodMk continuous_id
        exact hcont.comp hh
      smooth := fun k L hL hLf w => by
        have := hsm k 0 L continuous_zero hL (fun _ => by simp) hLf u w
        simpa using this }
  · intro b hb
    funext v
    rw [heis_right, ← extR_apply, map_nsmul, hv₂.2.1 _ (memR b hb)]
  · intro e he b hb hh
    funext v
    rw [heis_right, ← extR_apply, hv₂.2.2 e he _ (memR b hb) (extR_half B'.o e b hh)]

end GlobalTheory.ContrComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem besGrp_iff_sA (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (g : GA D (D.sp.Y 0)) :
    g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := by
  have hS : besGrp B.d B.o = (Formalism.L2.SG.Pf.SAsub X u).comap (iotaX X h).toMonoidHom := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := (B.tieN n).1 hn
        exact ⟨fun v => (h1 v).1, Formalism.L2.SG.Pf.nfin_sfin X u h2⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (B.tieH g).1 hg
        exact ⟨hinf_le_sinf X u _ h1, Formalism.L2.SG.Pf.hfin_sfin X u ⟨_, h2⟩⟩
    · intro g hg
      have hg' : (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := hg
      obtain ⟨hg1, hg2⟩ := hg'
      obtain ⟨hi, hhi, ni, hni, ei⟩ := Formalism.L2.SG.Pf.Sinf.levi X u hg1
      obtain ⟨hf, nf, hnf, ef⟩ := Formalism.L2.SG.Closed.FinLeviC_holds D X u _ hg2
      have hgeq : g = (iotaX X h).symm (hi, (hf : X.B.I.Gf)) * (iotaX X h).symm (ni, nf) := by
        rw [← map_mul, (iotaX X h).eq_symm_apply]
        exact Prod.ext ei ef
      rw [hgeq]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
      · refine (B.tieH _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hhi, hf.2⟩
      · refine (B.tieN _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hni, hnf⟩
  rw [hS]; rfl

theorem besGrp_eq_sGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A),
    (∀ g, g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u) ∧
      ∀ g, g ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o ↔ iotaX X h g ∈ Srat X u := by
  intro D X h u ψ A B
  refine ⟨besGrp_iff_sA D X h u ψ A B, fun g => ?_⟩
  rw [Subgroup.mem_inf, besGrp_iff_sA D X h u ψ A B, Formalism.L2.SG.Pf.srat_eq, Subgroup.mem_inf,
    Formalism.MainNotions.LeviCoordinates.rr_mem_GF, Formalism.IndefR.RationalEmbedding.iota_rat]
  have e : iotaX X h g = Formalism.L2.SG.RowsJoinPinned.castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e, castGA_mem_GFset]
  rfl

end GlobalTheory.Core.Mi

end
end


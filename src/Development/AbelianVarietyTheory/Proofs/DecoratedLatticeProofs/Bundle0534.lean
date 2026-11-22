import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqOfOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0504
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem gl₂_comm (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (a : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)
    (b : GL (Q'.n₂ ⊕ Fin (Q'.c + 1)) Q'.k) : Q₀.gl₂ a * Q'.gl₂ b = Q'.gl₂ b * Q₀.gl₂ a := by
  have h0 : Q₀.gl₂ a ∈ grpAt S.B'.V (· = Q₀.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q₀.k Q₀.q S.B'.V _ Q₀.F.G₂ Q₀.gl₂ Q₀.loc₂).2.1]; exact ⟨a, rfl⟩
  have h1 : Q'.gl₂ b ∈ grpAt S.B'.V (· = Q'.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q'.k Q'.q S.B'.V _ Q'.F.G₂ Q'.gl₂ Q'.loc₂).2.1]; exact ⟨b, rfl⟩
  exact GlobalTheory.SeeSawLastValue.grpAt_comm (fun p hp hp' => hne (hp.symm.trans hp')) h0 h1

theorem typed_trc (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (e : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k →₀ ℂ)
    {f : GA D S.B'.V → ℂ} (hf : Q'.Typed f) : Q'.Typed (trc (e.mapDomain Q₀.gl₂) f) := by
  classical
  intro j
  funext x
  have hj := hf j
  simp only [rTrans, Pi.smul_apply, smul_eq_mul, trc_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  have := congrFun hj (x * Q₀.gl₂ a)
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at this
  rw [mul_assoc x, ← gl₂_comm Q₀ Q' hne, ← mul_assoc, this]
  ring

theorem away_pair (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) {A T : HSp D} (c d : WO A T →₀ ℂ) (hc : Q'.Away c)
    (hd : ∀ u ∈ d.support, IsHalf (Q₀.q.e + cA D Q₀.q.e) u) : Q'.Away (aconv [c, d]) := by
  obtain ⟨ε₀, hε₀, he₀⟩ := Q₀.q.above
  obtain ⟨ε', hε', he'⟩ := Q'.q.above
  have horth : algebraMap (AF D.host.F) (AE D) ε' * algebraMap (AF D.host.F) (AE D) ε₀ = 0 := by
    rw [← map_mul, GlobalTheory.VacuumFrameCompare.place_orth hε' hε₀ (Ne.symm hne), map_zero]
  intro u hu i j
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_aconv_pair c d hu
  have h1 := hc a ha i j
  have h2 := hd b hb i j
  rw [he'] at h1 ⊢
  rw [he₀] at h2
  have h3 : (1 - algebraMap (AF D.host.F) (AE D) ε') * b i j = b i j := by
    rw [← h2, sub_mul, one_mul, ← mul_assoc, horth, zero_mul, sub_zero]
  rw [Matrix.add_apply, mul_add, h1, h3]

theorem hyps_succ {r : ℕ} (Q : Fin (r + 1) → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ} {f₁ : WO S.B.V S.J.W → ℂ} {f₂ : WO S.J.W S.B'.V → ℂ}
    {φ : GA D S.B.A → ℂ} {f : GA D S.B'.V → ℂ} {g : GA D S.B.V} {h₁ : GA D S.J.W} {h₂ : GA D S.B'.V}
    (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (γ : (Q 0).A₁) (β : (Q 0).A₂) :
    Hyps (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  obtain ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩ := hH
  have hne : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  have hP : ∀ v, places (fun i : Fin r => Q i.succ) v → places Q v := fun v ⟨i, hi⟩ => ⟨i.succ, hi⟩
  refine ⟨fun i => ⟨away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).1 ((Q 0).ent₁ γ).1,
      away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).2 ((Q 0).ent₂ γ β).1⟩, t1, t2, fun i => hv i.succ, hφ,
    contAut_trc _ hf, fun i => typed_trc (Q 0) (Q i.succ) (hne i) _ (ht i.succ),
    grpOff_anti D _ _ _ hP hg, grpOff_anti D _ _ _ hP hh₁, grpOff_anti D _ _ _ hP hh₂⟩

theorem trc_conv_cons {V : HSp D} (E : GA D V →₀ ℂ) (l : List (GA D V →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) (f : GA D V → ℂ) :
    trc (conv (E :: l)) f = trc (conv l) (trc E f) := by
  have e1 : conv (E :: l) =
      (MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ (GA D V)).coeff := by
    rw [← comm_conv E l h, ← conv_cons]
  rw [e1, trc_mul]

theorem sum_pi_succ {r : ℕ} {α : Fin (r + 1) → Type} [∀ i, Fintype (α i)] (F : (∀ i, α i) → ℂ) :
    ∑ γ, F γ = ∑ a : α 0, ∑ γ' : ∀ i : Fin r, α i.succ, F (Fin.cons a γ') := by
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem value_succ {r : ℕ} (Q : Fin (r + 1) → QStep S)
    (hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a)
    (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ)
    (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = ∑ p : (Q 0).A₁ × (Q 0).A₂, (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2) *
      value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
        (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  classical
  have hX : ∀ (γ0 : (Q 0).A₁) (β0 : (Q 0).A₂) (γ' : ∀ i : Fin r, (Q i.succ).A₁) (β' : ∀ i : Fin r, (Q i.succ).A₂),
      S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)))
        (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)
          ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i).e₂ ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i)).mapDomain (Q i).gl₂)) f)
        g h₁ h₂ =
      S.val (aconv (aconv [c₁, (Q 0).d₁ γ0] :: List.ofFn fun i => (Q i.succ).d₁ (γ' i)))
        (aconv (aconv [c₂, (Q 0).d₂ γ0 β0] :: List.ofFn fun i => (Q i.succ).d₂ (γ' i) (β' i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i.succ).e₂ (β' i)).mapDomain (Q i.succ).gl₂))
          (trc (((Q 0).e₂ β0).mapDomain (Q 0).gl₂) f)) g h₁ h₂ := by
    intro γ0 β0 γ' β'
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [aconv_pair_cons, aconv_pair_cons, trc_conv_cons]
    intro x hx e he y hy
    rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact hcomm i a b
  rw [Fintype.sum_prod_type]
  simp only [value]
  simp only [sum_pi_succ (α := fun i => ↥(Q i).A₁), sum_pi_succ (α := fun i => ↥(Q i).A₂)]
  simp only [hX]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ0 _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β0 _ => Finset.sum_congr rfl fun γ' _ => Finset.sum_congr rfl fun β' _ => ?_
  ring

theorem outer : ∀ (D : D7) (r : ℕ), ValQr D r → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ μ₁ ρ₁ μ₂ ρ₂, Norm (fun i => Q i.succ) μ₁ ρ₁ μ₂ ρ₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) := by
  intro D r IH ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  have hinj' : Function.Injective fun i : Fin r => (Q i.succ).q.v := hinj.comp (Fin.succ_injective _)
  have hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a :=
    fun i => gl₂_comm (Q 0) (Q i.succ) fun h => Fin.succ_ne_zero i (hinj h).symm
  have key := GlobalTheory.SeeSaw.VanMany.iteratedQuotientIntegral_finite_linearCombination ρ₁ μ₁ ρ₂ μ₂ (I := (Q 0).A₁ × (Q 0).A₂)
    (fun p => (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2))
    (fun p x y => integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ x.1 y.1)
    (fun p => value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂)
    (fun p => IH ψ hψ σ S (fun i => Q i.succ) hinj' μ₁ ρ₁ μ₂ ρ₂ hN _ _ f₁ f₂ φ _ g h₁ h₂ (hyps_succ Q hinj hH p.1 p.2))
  rw [value_succ Q hcomm]
  convert key using 1
  funext x y
  simp only [innerVal, Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

end GlobalTheory.QValOuter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastWittLineOfBesselJacobiLatticesGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

def SameAt (v : GlobalTheory.FinPl.Pl D) (𝔞 𝔟 : FI D) : Prop := ∀ s ∈ idAt D (· = v), s ∈ idV 𝔞 v ↔ s ∈ idV 𝔟 v

theorem mem_idAt_of_idV {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔞 : FI D}
    {s : AE D} (hs : s ∈ idV 𝔞 v) : s ∈ idAt D (· = v) := by
  have h3 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.2.1 𝔞 1 one_ne_zero s
  rw [FractionalIdeal.spanSingleton_one, one_mul] at h3
  exact (h3.1 hs).2

theorem sameAt_div {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔞 𝔞' 𝔟 𝔟' : FI D}
    (ha : 𝔞 ≠ 0) (ha' : 𝔞' ≠ 0) (hb : 𝔟 ≠ 0) (hb' : 𝔟' ≠ 0) (h𝔞 : SameAt v 𝔞 𝔞') (h𝔟 : SameAt v 𝔟 𝔟') :
    SameAt v (𝔟 * 𝔞⁻¹) (𝔟' * 𝔞'⁻¹) := by
  intro s hs
  have h2 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1
  rw [← h2 _ _ ha hb s hs, ← h2 _ _ ha' hb' s hs]
  constructor
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    exact (h𝔟 _ (Ideal.mul_mem_left _ s haA)).1 (h a ((h𝔞 a haA).2 haV))
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    exact (h𝔟 _ (Ideal.mul_mem_left _ s haA)).2 (h a ((h𝔞 a haA).1 haV))

theorem sameAt_trans {v : GlobalTheory.FinPl.Pl D} {𝔞 𝔟 𝔠 : FI D} (h1 : SameAt v 𝔞 𝔟) (h2 : SameAt v 𝔟 𝔠) : SameAt v 𝔞 𝔠 :=
  fun s hs => (h1 s hs).trans (h2 s hs)

theorem sameAt_refl (v : GlobalTheory.FinPl.Pl D) (𝔞 : FI D) : SameAt v 𝔞 𝔞 := fun _ _ => Iff.rfl

theorem sameAt_mul_of_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {v : GlobalTheory.FinPl.Pl D} {𝔠 𝔫 : FI D}
    (hc : 𝔠 ≠ 0) (hn : 𝔫 ≠ 0) (h : SameAt v 1 𝔫) : SameAt v 𝔠 (𝔠 * 𝔫) := by
  have h1 : SameAt v (1 * 1⁻¹) (1 * 𝔫⁻¹) :=
    sameAt_div hψ one_ne_zero hn one_ne_zero one_ne_zero h (sameAt_refl v 1)
  have h2 := sameAt_div hψ (by simp) (by simpa using hn) hc hc h1 (sameAt_refl v 𝔠)
  simpa using h2

def col {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : Fin S.rank → D.host.E := fun k => d.e k i

theorem colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    colMul d.jX i a = a • ratV (col d i) := by
  funext k
  rfl

theorem col_ne_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : col d i ≠ 0 := by
  intro h
  have h' : ∀ k, d.e k i = 0 := fun k => congrFun h k
  have := congrFun (congrFun d.e'e i) i
  simp [Matrix.mul_apply, h'] at this

theorem vecB_ne_zero {S₀ A L : HSp D} (o : OrthDec S₀ A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) :
    vecB o ζ ≠ 0 := by
  intro h
  apply hζ.2
  rw [← o.isoB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have : o.iB *ᵥ ζ = 0 := h
  rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

theorem smul_colMul' {m n : ℕ} (x : Mx D m n) (i : Fin n) (s t : AE D) : s • colMul x i t = colMul x i (s * t) := by
  funext k
  simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem cols_sameAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : GlobalTheory.FinPl.Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (i : Fin ρ) {𝔢 𝔟 : FI D} (h𝔟0 : 𝔟 ≠ 0)
    (h𝔢 : ∀ a ∈ idAt D (· = v), a • ratV (col B.d i) ∈ latV B.V LV (· = v) ↔ a ∈ idV 𝔢 v)
    (h𝔟 : ∀ a ∈ idAt D (· = v), a • ratV (col J.d i) ∈ latV J.W LW (· = v) ↔ a ∈ idV 𝔟 v) :
    SameAt v 𝔢 (𝔟 * (D.host.AA : FI D)) := by
  intro a ha
  obtain ⟨-, h2, -, -, -, -, h7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hAA : (D.host.AA : FI D) ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  rw [← h𝔢 a ha, ← colMul_jX, hG.cols i a ha, h7]
  have e : 𝔟 * (D.host.AA : FI D) = 𝔟 * ((D.host.AA : FI D)⁻¹)⁻¹ := by rw [inv_inv]
  rw [e, ← h2 _ _ (inv_ne_zero hAA) h𝔟0 a ha]
  constructor
  · rintro ⟨-, h⟩ t ht
    have htA := mem_idAt_of_idV hψ ht
    have h' := h t ht
    rw [smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha)] at h'
    rw [mul_comm]; exact h'
  · intro h
    refine ⟨fun k => Ideal.mul_mem_right _ _ ha, fun t ht => ?_⟩
    have htA := mem_idAt_of_idV hψ ht
    rw [smul_colMul', show xZero J.d = J.d.jX from rfl, colMul_jX, h𝔟 _ (Ideal.mul_mem_left _ t ha), mul_comm]
    exact h t ht

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

open GlobalTheory.SeeSaw.LastPrim in
set_option maxHeartbeats 1000000 in

theorem last_sameAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : GlobalTheory.FinPl.Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (i : Fin ρ) (hi : i.1 + 1 = ρ) {𝔷 : FI D} {𝔟 : ℕ → FI D}
    (h𝔷0 : 𝔷 ≠ 0) (h𝔷 : GlobalTheory.SeeSaw.LineId B.o B.ζ LV₀ 𝔷 v) (h𝔟0 : 𝔟 i ≠ 0) (hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v) :
    SameAt v 1 (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷) := by
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  obtain ⟨n, hn⟩ := i
  simp only at hi
  obtain rfl : n = ρ - 1 := by omega
  set i : Fin ρ := ⟨ρ - 1, hn⟩ with hi_def
  have hρ : 0 < ρ := by omega
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hL := colMul_jY_mem_latA_iff D ψ hψ J.W J.W₀ ρ J.d LW (𝔟 i) v i h𝔟0
    (GlobalTheory.T.dualIsotropicLine_mem_completion_iff D ψ hψ J.W J.W₀ ρ J.d LW LW₀ 𝔟 v hG.sdW hmono i h𝔟0)
  set 𝔑 : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) with h𝔑
  have h𝔑0 : 𝔑 ≠ 0 := mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ)
    (mul_ne_zero hAAb (inv_ne_zero h𝔟0))
  have e : (D.host.AAbar : FI D) * (𝔟 i)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔑 := by
    rw [h𝔑, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  have e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1 := by
    rw [← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]
  have key : ∀ a ∈ idAt D (· = v), ∀ y ∈ latV B.V₀ LV₀ (· = v),
      (Matrix.mulVec (show Matrix (Fin J.W.rank) (Fin B.V₀.rank) (AE D) from
        J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ))) y ∈ GlobalTheory.FinPl.latA J.W LW (· = v) ↔
        a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idV 𝔑 v) := by
    intro a ha y hy
    have hzi : (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l) ∈ idAt D (· = v) :=
      sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)
    rw [incAdj_yZero_mulVec D ρ B J hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, cA_cA,
      GlobalTheory.DualPairCheck.cA_incA, e, h3 _ _ (inv_ne_zero hξ)]
    have e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a *
        cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) =
        -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) := by
      rw [← mul_assoc, ← mul_assoc, e3]; ring
    rw [e4, neg_mem_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩
  intro a ha
  have e5 : 𝔑 * 𝔷 = 𝔑 * 𝔷⁻¹⁻¹ := by rw [inv_inv]
  rw [h1, ← hG.last hρ a ha, GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW, e5,
    ← h2 _ _ (inv_ne_zero h𝔷0) h𝔑0 a ha]
  constructor
  · rintro ⟨-, hu⟩ g hg
    obtain ⟨y, hy, hyg⟩ := GlobalTheory.T.hermitianPairing_onto_inverseIdeal_at_place D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 g hg
    rw [← hyg]
    exact (key a ha y hy).1 (hu y hy)
  · intro h
    have hcA : cA D a ∈ idAt D (· = v) := cA_mem_idAt'' ha
    refine ⟨fun k l => ?_, fun y hy => (key a ha y hy).2 (h _ (GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion D ψ hψ B.V₀ B.A B.L B.o B.ζ LV₀ 𝔷 v hG.sdV₀ h𝔷 h𝔷0 y hy))⟩
    have e6 := congrFun (incAdj_yZero_mulVec D ρ B J hρ a (Pi.single l 1)) k
    rw [Matrix.mulVec_single_one] at e6
    refine (congrArg (· ∈ idAt D (· = v)) e6).mpr ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))

end GlobalTheory.Core.Mi.ChainLast

namespace GlobalTheory.Core.Mi.ChainLast

variable {D : D7}

theorem ideal_eq (𝔟 𝔷 : FI D) (h𝔟0 : 𝔟 ≠ 0) (h𝔷0 : 𝔷 ≠ 0) :
    𝔟 * (D.host.AA : FI D) * 𝔷⁻¹ *
      (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * 𝔟⁻¹) * 𝔷) = GlobalTheory.SeeSaw.dI D := by
  calc 𝔟 * (D.host.AA : FI D) * 𝔷⁻¹ *
        (FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * 𝔟⁻¹) * 𝔷)
      = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA : FI D) * (D.host.AAbar : FI D) * (𝔟 * 𝔟⁻¹) *
          (𝔷 * 𝔷⁻¹) := by ring
    _ = GlobalTheory.SeeSaw.dI D := by rw [mul_inv_cancel₀ h𝔟0, mul_inv_cancel₀ h𝔷0, mul_one, mul_one]; rfl

end GlobalTheory.Core.Mi.ChainLast

open GlobalTheory.Core.Mi.ChainLast in

theorem GlobalTheory.Core.Mi.LatMatch.lastAt_of_goodBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : GlobalTheory.FinPl.Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → LastAt ψ B.d (vecB B.o B.ζ) LV LV₀ v := by
  intro D ψ hψ ρ B J LV LV₀ LW LW₀ v hG i hi s hs
  obtain ⟨-, h2, -, -, h5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  obtain ⟨𝔢, h𝔢0, -, h𝔢⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D B.V LV (col B.d i) hG.sdV (col_ne_zero _ _)
  obtain ⟨𝔷, h𝔷0, -, h𝔷⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D B.V₀ LV₀ (vecB B.o B.ζ) hG.sdV₀ (vecB_ne_zero B.o B.line)
  let 𝔟 : ℕ → FI D := fun n => if h : n < ρ then
    Classical.choose (GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D J.W LW (col J.d ⟨n, h⟩) hG.sdW (col_ne_zero _ _)) else 1
  have h𝔟 : ∀ j : Fin ρ, 𝔟 j ≠ 0 ∧
      ∀ a ∈ idAt D (· = v), a • ratV (col J.d j) ∈ latV J.W LW (· = v) ↔ a ∈ idV (𝔟 j) v := by
    intro j
    have hs := Classical.choose_spec (GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D J.W LW (col J.d j) hG.sdW (col_ne_zero _ _))
    simp only [𝔟, dif_pos j.2, Fin.eta]
    exact ⟨hs.1, hs.2.2 v⟩
  have hmono : GlobalTheory.SeeSaw.MonoId J.d LW LW₀ 𝔟 v :=
    ⟨hG.monoW, fun j a ha => by rw [colMul_jX]; exact (h𝔟 j).2 a ha⟩
  have hA := cols_sameAt hψ hG i (h𝔟 i).1 (h𝔢 v) (h𝔟 i).2
  have hB := last_sameAt hψ hG i hi h𝔷0 (h𝔷 v) (h𝔟 i).1 hmono
  have hAA : (D.host.AA : FI D) ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hb0 : 𝔟 i * (D.host.AA : FI D) ≠ 0 := mul_ne_zero (h𝔟 i).1 hAA
  have hN0 : FractionalIdeal.spanSingleton _ D.host.xi0 * ((D.host.AAbar : FI D) * (𝔟 i)⁻¹) * 𝔷 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hξ)
      (mul_ne_zero hAAb (inv_ne_zero (h𝔟 i).1))) h𝔷0
  have hC := sameAt_div hψ h𝔷0 h𝔷0 h𝔢0 hb0 (sameAt_refl v 𝔷) hA
  have hD := sameAt_mul_of_one hψ (mul_ne_zero hb0 (inv_ne_zero h𝔷0)) hN0 hB
  rw [ideal_eq (𝔟 i) 𝔷 (h𝔟 i).1 h𝔷0] at hD
  rw [← h5 s hs, ← sameAt_trans hC hD s hs, ← h2 𝔷 𝔢 h𝔷0 h𝔢0 s hs]
  constructor
  · intro h a haV
    have haA := mem_idAt_of_idV hψ haV
    have h' := h a haA ((h𝔷 v a haA).2 haV)
    rwa [colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)] at h'
  · intro h a haA haz
    rw [colMul_jX, h𝔢 v _ (Ideal.mul_mem_left _ s haA)]
    exact h a ((h𝔷 v a haA).1 haz)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → ∀ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1) → ∀ P Q, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q)‖ ≤ C * (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g)) ^ ((W.rank : ℝ) / 2) := by
  first | exact @GlobalTheory.TwBound.tw_bound | exact GlobalTheory.TwBound.tw_bound | (intros; apply GlobalTheory.TwBound.tw_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedThetaPairingIdentityStatement
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
theorem _root_.GlobalTheory.T.regularised_theta_pairing_identity : GlobalTheory.Published.DoublingMethod → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → ∀ u ∈ A0 θ A cA, GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) ∧ GlobalTheory.Eis.EisContinues A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) ∧ (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) g) (rightOf (A.rank / 2))) ∧ (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) s₀ k) ∧ ∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s) m ∧ GlobalTheory.Eis.zeta A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) s = ∫ g, integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s g ∂m := by
  first | exact @GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand | exact GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand | (intros; apply GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.LastOneLin.lin | exact GlobalTheory.LastOneLin.lin | (intros; apply GlobalTheory.LastOneLin.lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLastTwoSteps_doubleLiftPeriod_value : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → LastLaw D → SeeLast D → FlatLaw D → BiAct D → ValLastX t := by
  first | exact @GlobalTheory.SeeSawLastValue.valLast | exact GlobalTheory.SeeSawLastValue.valLast | (intros; apply GlobalTheory.SeeSawLastValue.valLast <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchinoStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_fockDoubledPair_of_weil_and_ichino : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → ∀ D : D7, SiegelWeilFock D := by
  first | exact @GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses | exact GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses | (intros; apply GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralEqSiegelEisensteinOfWeilRange
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem thetaMean_eq_eis_of_weil : GlobalTheory.Published.WeilSiegelFormulaUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 2 * A.rank < B.rank → (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) → ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ φ : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B φ → (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧ GlobalTheory.ThetaMean.thetaMean omh mH φ = GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) := by
  intro hWeil D ψ A B ha hb hwitt χB omh homh ν 𝓕 hcov mH hmH φ hφ
  have hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hwitt
  obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt'
  obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
  refine ⟨hint, ?_⟩
  obtain ⟨-, h2⟩ := hser hb ν 𝓕 hcov
  funext g
  rw [← swSection_eq_swSec]
  exact ((h2 g).2).symm

end GlobalTheory.Core.Rk.IP
end


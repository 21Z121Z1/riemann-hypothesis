import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0565
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0563
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0564
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ContrOpProof

variable {D : D7}

theorem mxAt_mul_right {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem mxAt_mul_left {P : Pl D → Prop} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : MxAt P u) :
    MxAt P (N * u) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hu k j)

theorem mxAt_sub {P : Pl D → Prop} {m n : ℕ} {u v : Mx D m n} (hu : MxAt P u) (hv : MxAt P v) : MxAt P (u - v) :=
  fun i j => by simpa only [Matrix.sub_apply] using Ideal.sub_mem _ (hu i j) (hv i j)

theorem mxAt_neg {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : MxAt P (-u) :=
  fun i j => by simpa only [Matrix.neg_apply] using Submodule.neg_mem _ (hu i j)

theorem fin_of_mxAt {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem biComb_single (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S) (a' : WO S A') (r : ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' (Finsupp.single a r) (Finsupp.single a' 1) C u v =
      r * heisO ψ A S a (fun u' => heisO ψ S A' a' (C u') v) u := by
  by_cases hr : r = 0
  · subst hr
    simp [biComb, comb]
  · simp [biComb, comb, Finsupp.support_single_ne_zero _ hr]

theorem symplOH_self {S T : HSp D} (x : WO S T) : symplOH S T x (-x) = 0 := by
  have h1 := GlobalTheory.SplitScalar.symplOH_skew S T x x
  have h2 := GlobalTheory.SplitScalar.symplOH_add_self S T x x
  have h3 : symplO S T x x = 0 := by
    rw [← h2]
    nth_rewrite 2 [h1]
    exact add_neg_cancel _
  have h4 : symplOH S T x x = 0 := by rw [symplOH, h3, mul_zero]
  have h5 := GlobalTheory.SplitScalar.symplOH_add_right S T x x (-x)
  rw [add_neg_cancel, GlobalTheory.ContrComb.symplOH_zero_right, h4, zero_add] at h5
  exact h5.symm

theorem heisO_neg_cancel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T (-x) g) = g := by
  rw [GlobalTheory.SplitScalar.heisO_heisO, add_neg_cancel, GlobalTheory.SplitScalar.heisO_zero, symplOH_self, AddChar.map_zero_eq_one,
    one_smul]

theorem line_step {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ)
    (hf₁ : IsThetaFunO ψ B.V₀ S f₁) (hf₂ : IsThetaFunO ψ S B'.V₀ f₂) (y : WO B.L S) (w : WO S B'.L)
    (hy : ((B.o.resS S).symm (0, y)).map (infPart D) = 0)
    (hk : (-(B.o.resS S).symm (0, l.κ S w)).map (infPart D) = 0) (c : ℂ)
    (hc : GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y - l.κ S w)) f₁) f₂ =
      c • GlobalTheory.Unf.contr l S vL f₁ f₂) :
    GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, w)) f₂) =
      (ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S w)) ((B.o.resS S).symm (0, y))) * c) •
        GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S (-(B.o.resS S).symm (0, l.κ S w))
      (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁)) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hk (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hy hf₁)
  have hmove := GlobalTheory.T.besselLineContraction_heisenberg_invariant D ψ hψ ρ σ B B' l S vL _ f₂ hth hf₂ w
  rw [heisO_neg_cancel] at hmove
  rw [hmove, GlobalTheory.SplitScalar.heisO_heisO, contr_smul_left]
  have he : -(B.o.resS S).symm (0, l.κ S w) + (B.o.resS S).symm (0, y) = (B.o.resS S).symm (0, y - l.κ S w) := by
    rw [← map_neg, ← map_add, Prod.neg_mk, neg_zero, Prod.mk_add_mk, zero_add, neg_add_eq_sub]
  rw [he, hc, smul_smul]

open Classical in

def cstL (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop)
    (y : WO B.L S) : ℂ :=
  if (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P then
    (if h : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f
      then h.choose else 0) else 0

def coefL (ψ : AddChar (AF D.host.F) ℂ) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop) (u : WO B.V₀ S) (u' : WO S B'.V₀) : ℂ :=
  ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S (B'.o.resT S u').2)) ((B.o.resS S).symm (0, (B.o.resS S u).2))) *
    cstL ψ B S M LS P ((B.o.resS S u).2 - l.κ S (B'.o.resT S u').2)

set_option maxHeartbeats 2000000 in
theorem contrOp : ∀ D : D7, ContrOp D := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr e₁ e₂ he₁ he₂
  classical
  have key : ∀ y, MxAt P y → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ =
        cstL ψ B S M LS P y • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
    intro y hy f₁ f₂ h₁ h₂
    by_cases hin : (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P
    · have hex : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f := by
        obtain ⟨c, hc⟩ := GlobalTheory.T.halfGenerated_point_acts_scalar_on_latticeVacua D ψ B.V₀ S _ _ (GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves D k ι p I P hP B.V₀ S _ _ _ hin)
        exact ⟨c, fun f hf => hc f hf.2⟩
      have hcst : cstL ψ B S M LS P y = hex.choose := by simp only [cstL, if_pos hin, dif_pos hex]
      rw [hcst, hex.choose_spec f₁ h₁, contr_smul_left]
    · have hcst : cstL ψ B S M LS P y = 0 := by simp only [cstL, if_neg hin]
      rw [hcst, zero_smul, GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction D k ι p I P hP n' n'' ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr
        y hy hin f₁ f₂ h₁ h₂]
  let s := e₁.support ×ˢ e₂.support
  refine ⟨⟨s.card, fun i => Finsupp.single (B.o.resS S (s.equivFin.symm i).1.1).1
      (e₁ (s.equivFin.symm i).1.1 * e₂ (s.equivFin.symm i).1.2 *
        coefL ψ B B' l S M LS P (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2),
    fun i => Finsupp.single (B'.o.resT S (s.equivFin.symm i).1.2).1 1⟩, ?_, ?_⟩
  · intro i
    have hq := (s.equivFin.symm i).2
    rw [Finset.mem_product] at hq
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_right (he₁ _ hq.1) _
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_left _ (he₂ _ hq.2)
  intro f₁ f₂ h₁ h₂
  have hth₁ : ∀ u, MxAt P u → IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S u f₁) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₁.1
  have hth₂ : ∀ u, MxAt P u → IsThetaFunO ψ S B'.V₀ (heisO ψ S B'.V₀ u f₂) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₂.1
  have hint : ∀ g₁ g₂, IsThetaFunO ψ B.V₀ S g₁ → IsThetaFunO ψ S B'.V₀ g₂ → ∀ (u : WO B.A S) (v : WO S B'.A),
      IntegrableOn (fun x => g₂ ((B'.o.resT S).symm (v, x)) * g₁ ((B.o.resS S).symm (u, l.κ S x))) vL.𝓕 vL.μ := by
    intro g₁ g₂ hg₁ hg₂ u v
    obtain ⟨hc, hp⟩ := GlobalTheory.T.theta_contraction_integrand_continuous_periodic D ρ σ B B' l S ψ g₁ g₂ hg₁ hg₂
    exact (GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
      (fun x q => g₂ ((B'.o.resT S).symm (q.2, x)) * g₁ ((B.o.resS S).symm (q.1, l.κ S x))) hc
      (fun γ' hγ x q => hp γ' hγ x q.1 q.2)).1 (u, v)
  have hLR : ∀ (g₁ : WO B.V₀ S → ℂ) (g₂ : WO S B'.V₀ → ℂ) (b : WO B.A S) (b' : WO S B'.A),
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (b, 0)) g₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b', 0)) g₂) =
        fun u₀ v₀ => heisO ψ B.A S b (fun u'' => heisO ψ S B'.A b' (GlobalTheory.Unf.contr l S vL g₁ g₂ u'') v₀) u₀ := by
    intro g₁ g₂ b b'
    funext u₀ v₀
    rw [← GlobalTheory.ContrComb.heis_left ψ l S vL g₁ _ b u₀ v₀]
    congr 1
    funext u''
    rw [GlobalTheory.ContrComb.heis_right]
  have heL : ∀ z : WO B.L S, MxAt P z → MxAt P ((B.o.resS S).symm (0, z)) := by
    intro z hz
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right hz _
  have pair : ∀ u, MxAt P u → ∀ u', MxAt P u' →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) =
        fun u₀ v₀ => coefL ψ B B' l S M LS P u u' * heisO ψ B.A S (B.o.resS S u).1
          (fun u'' => heisO ψ S B'.A (B'.o.resT S u').1 (GlobalTheory.Unf.contr l S vL f₁ f₂ u'') v₀) u₀ := by
    intro u hu u' hu'
    have hsL : u = (B.o.resS S).symm ((B.o.resS S u).1, 0) + (B.o.resS S).symm (0, (B.o.resS S u).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hsR : u' = (B'.o.resT S).symm ((B'.o.resT S u').1, 0) + (B'.o.resT S).symm (0, (B'.o.resT S u').2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hoL : symplO B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0)) ((B.o.resS S).symm (0, (B.o.resS S u).2)) = 0 := by
      rw [B.o.symplO_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hoR : symplO S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0)) ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) = 0 := by
      rw [B'.o.symplO_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hy : MxAt P (B.o.resS S u).2 := mxAt_mul_right hu _
    have hw : MxAt P (B'.o.resT S u').2 := mxAt_mul_left _ hu'
    have hkw : MxAt P (l.κ S (B'.o.resT S u').2) := GlobalTheory.T.besselLink_kappa_preserves_supported_matrices D ρ B B'.L B'.ζ l S P _ hw
    have hline := line_step ψ hψ l S vL f₁ f₂ h₁.1 h₂.1 (B.o.resS S u).2 (B'.o.resT S u').2 (fin_of_mxAt (heL _ hy))
      (fin_of_mxAt (mxAt_neg (heL _ hkw))) _ (key _ (mxAt_sub hy hkw) f₁ f₂ h₁ h₂)
    have e1 : heisO ψ B.V₀ S u f₁ = heisO ψ B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0))
        (heisO ψ B.V₀ S ((B.o.resS S).symm (0, (B.o.resS S u).2)) f₁) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoL, ← hsL]
    have e2 : heisO ψ S B'.V₀ u' f₂ = heisO ψ S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0))
        (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) f₂) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoR, ← hsR]
    rw [e1, e2, hLR, hline]
    funext u₀ v₀
    simp only [coefL, heisO, Pi.smul_apply, smul_eq_mul]
    ring
  funext u₀ v₀
  have hexp : GlobalTheory.Unf.contr l S vL (comb ψ _ _ e₁ f₁) (comb ψ _ _ e₂ f₂) u₀ v₀ =
      ∑ u' ∈ e₂.support, ∑ u ∈ e₁.support, (e₂ u' * e₁ u) *
        GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) u₀ v₀ := by
    simp only [GlobalTheory.Unf.contr, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    have hI : ∀ u' ∈ e₂.support, ∀ u ∈ e₁.support, IntegrableOn (fun x =>
        e₂ u' * heisO ψ S B'.V₀ u' f₂ ((B'.o.resT S).symm (v₀, x)) *
          (e₁ u * heisO ψ B.V₀ S u f₁ ((B.o.resS S).symm (u₀, l.κ S x)))) vL.𝓕 vL.μ := by
      intro u' hu' u hu
      refine Integrable.congr ((hint _ _ (hth₁ u (he₁ u hu)) (hth₂ u' (he₂ u' hu')) u₀ v₀).const_mul (e₂ u' * e₁ u))
        (ae_of_all _ fun x => ?_)
      simp only
      ring
    rw [integral_finset_sum _ fun u' hu' => integrable_finset_sum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [integral_finset_sum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hexp, Finset.sum_comm]
  simp only [BiOp.app, Finset.sum_apply]
  rw [Equiv.sum_comp s.equivFin.symm (fun q : s => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1.1).1 (e₁ q.1.1 * e₂ q.1.2 * coefL ψ B B' l S M LS P q.1.1 q.1.2))
      (Finsupp.single (B'.o.resT S q.1.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀),
    Finset.sum_coe_sort s (fun q => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1).1 (e₁ q.1 * e₂ q.2 * coefL ψ B B' l S M LS P q.1 q.2))
      (Finsupp.single (B'.o.resT S q.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀), Finset.sum_product]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
  rw [pair u (he₁ u hu) u' (he₂ u' hu'), biComb_single]
  ring

end GlobalTheory.FinPl.ContrOpProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConvergentInnerProductConjugateOrientationWeil
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.IP

variable {D : D7}

theorem integrable_star_comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ := by
  simpa using (Complex.conjCLE.toContinuousLinearMap).integrable_comp hf

theorem memL2_conj_comp (V : HSp D) (μ : Measure (GA D V)) {f : GA D V → ℂ}
    (hf : MemL2Quotient (GQ V) μ f) : MemL2Quotient (GQ V) μ (fun x => conj (f x)) := by
  refine ⟨fun γ hγ g => by simp only [hf.1 γ hγ g], ?_⟩
  have := (Complex.conjCLE.toContinuousLinearMap).comp_memLp' hf.2
  convert this using 1
  funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem petersson_star_comp (V : HSp D) (μ : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    petersson V μ (fun x => conj (f₁ x)) (fun x => conj (f₂ x)) = conj (petersson V μ f₁ f₂) := by
  simp only [petersson, pet]
  rw [← integral_conj]
  congr 1; funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem innerProduct_convergent_conj : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  intro hRD hWS hSE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hw ht hK hm hν hf₁ hf₂
  obtain ⟨om, Φ₁, Φ₂, hW, hF₁, hF₂, -, -, hK₁, hK₂, μ, 𝓕, hcov, hc⟩ := hK
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions D θ A sA hS.2.2.2.1 hS.2.2.2.2.2.2.1
  have hP : Pair ψ θ A B χA χB sA sB t cA a om μ 𝓕 := ⟨hS, ha, ha', hW, hcov⟩
  obtain ⟨hU₁, hU₂, hI, hE⟩ := GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range hRD hWS hSE D ψ θ A B χA χB sA sB t cA a om μ 𝓕 hP hw ht m ν hm hν
    Φ₁ Φ₂ hF₁ hF₂ f₁ hf₁ f₂ hf₂
  have hcg : ∀ g, c g = conj (wcoef om μ 𝓕 Φ₁ Φ₂ g) := by
    intro g
    have h1 : wcoef om μ 𝓕 Φ₁ Φ₂ g = conj (c g) := by
      have h2 := hc g
      simp only at h2
      rw [h2]; rfl
    rw [h1, Complex.conj_conj]
  have hlift : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K u = fun h => conj (up om m Φ u h) := by
    intro K Φ u hK; funext h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift, up, petersson, pet, hK]
    rw [← integral_conj]
    congr 1; funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend]
  have hconv : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) → UpConv om m ν Φ u → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K u := by
    intro K Φ u hK hU
    refine ⟨fun h => ?_, ?_⟩
    · have := integrable_star_comp (hU.1 h)
      convert this using 2 with q
      simp [GlobalTheory.AutomorphicL2Unitary.descend, hK]
    · rw [hlift K Φ u hK]
      exact memL2_conj_comp B ν hU.2
  refine ⟨hconv K₁ Φ₁ f₁ hK₁ hU₁, hconv K₂ Φ₂ f₂ hK₂ hU₂, ?_, ?_⟩
  · have := integrable_star_comp hI
    convert this using 2 with g
    simp [hcg, rcoef]
  · rw [hlift K₁ Φ₁ f₁ hK₁, hlift K₂ Φ₂ f₂ hK₂, petersson_star_comp, hE, map_mul, ← integral_conj]
    simp [hcg, rcoef]

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLift_comm_levelPrimeOperators : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  first | exact @GlobalTheory.SeeSaw.liftS_of_exact | exact GlobalTheory.SeeSaw.liftS_of_exact | (intros; apply GlobalTheory.SeeSaw.liftS_of_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDat

theorem exists_o {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := GlobalTheory.SeeSaw.LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hTm a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hTm

theorem idem_eq {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.LocMod.PinInhab.idem_unique (hes _ (pl i).2) (ha i)

theorem isThetaAt_smul {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ} {f₀ Φ f : Mx D m n → ℂ}
    {κ : ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ B hs e Λ c f₀ (κ • Φ) f) : IsThetaAt ψ B hs e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨hex, hall⟩ := h
  refine ⟨hex, fun Tm hTm => ?_⟩
  rw [hall Tm hTm, map_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.MidDat

open GlobalTheory.MidDat in
theorem GlobalTheory.MidDat.moved_datum_prod : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((pk W).vac j)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  have ha : ∀ i, j + ((G i).s - j) = (G i).s := fun i => by have := (G i).hs; omega
  have hA := GlobalTheory.T.descent_data_step_exponents D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj (fun i => (G i).s - j) ha
  obtain ⟨κ, hκ, hdat⟩ := hA
  have ho : ∀ i, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ x ∈ o.support, IsHalf ((G i).q.e + cA D (G i).q.e) x) ∧
      ∀ Tm, (ofSplit (G i).q).IsModel f.c.ψ ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit (G i).q).up ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) x ∈ latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) (· = (G i).q.v)} (fun _ => 1) →
        Tm Φ₁ = comb f.c.ψ (Yc D j) (Yc D (j + 1)) o (Tm Φ₀) := fun i => exists_o hstd (G i).q _ _ hM hM'
  choose o ho1 ho2 using ho
  let Lp : Fin n → LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M' := fun i =>
    { k := (G i).k, q := (G i).q, unit := (G i).unit, Y := _, Y' := _,
      FS := (G i).FY j ((G i).s - j + 1) (by have := ha i; omega), FT := (G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega),
      Φ := ⟨((G i).S.T (Fin D.R.t)).Phi j ((G i).s - j) (ha i), (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ (ha i)⟩,
      e := (G i).eg j, e_is := (G i).eg_is j _ (ha i), o := o i, o_at := ho1 i, o_is := ho2 i }
  refine ⟨κ, hκ, Lp, fun i => rfl, fun i => rfl, fun i => ⟨(G i).latY _ _ _, (G i).latY _ _ _⟩, fun d hd => ?_⟩
  obtain ⟨-, e, he, hθ⟩ := hd.2
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sdY : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((pk W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
  have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hvth : IsThetaFunO (pk W).ψ _ _ ((pk W).vac j) := hd₀.2.1.2.theta
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((pk W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hRead.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((pk W).ΛY j) M ((pk W).ΛY (j + 1)) M' (sdY j (by omega)) hM (sdY (j + 1) hj) hM'
    _ hb _ hb' hmv hmv' e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) hvth hcth hθ
  subst hee
  have hfun : (fun x => (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧
          IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then
        omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B) ((pk W).chi (j + 1))
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) *
          omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)))
        else 0)) = κ • prodDat Lp := funext fun x => hdat x
  rw [hfun] at hmove
  refine ⟨κ⁻¹ • (pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((pk W).vac j)),
    GlobalTheory.OrientedHeis.theta_smul _ (hWe.om_pres _ _ hcth), isThetaAt_smul hκ hmove, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hκ, one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProoStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  first | exact @GlobalTheory.FinPl.vertexAll | exact GlobalTheory.FinPl.vertexAll | (intros; apply GlobalTheory.FinPl.vertexAll <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvariStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u y yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb → ∀ d₁ d₂, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) d₁ (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb) → (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM d₂ (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁]) (aconv [c₂, d₂]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QPl.LastOrb.orb | exact GlobalTheory.QPl.LastOrb.orb | (intros; apply GlobalTheory.QPl.LastOrb.orb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPointsStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placed_bessel_points : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, IsAt f B a₀ a := by
  first | exact @GlobalTheory.MiTop.exists_isAt | exact GlobalTheory.MiTop.exists_isAt | (intros; apply GlobalTheory.MiTop.exists_isAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatum_exists_at_levelPrimePlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  first | exact @GlobalTheory.LastSeeSawDatum.lastDatum | exact GlobalTheory.LastSeeSawDatum.lastDatum | (intros; apply GlobalTheory.LastSeeSawDatum.lastDatum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.QPl.LastPt.kernel_eq_sum | exact GlobalTheory.QPl.LastPt.kernel_eq_sum | (intros; apply GlobalTheory.QPl.LastPt.kernel_eq_sum <;> assumption)
end


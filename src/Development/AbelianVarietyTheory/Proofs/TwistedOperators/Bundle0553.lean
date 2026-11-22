import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.FockConjNeg

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO (GlobalTheory.Grid.neg S) T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id g) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z g) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem cplxO_neg_left {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT u = -cplxO sS sT u := by
  simp [cplxO, Matrix.mul_neg, smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem aPlus_cj_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {g : WO (GlobalTheory.Grid.neg S) T → ℂ} (hg : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T g) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cj id (aPlus (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-sS) sT) u g) =
      aPlus (heisO ψ S T) θ τ (cplxO sS sT) u (cj id g) := by
  have hn := GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hg τ (cplxO sS sT u)
  unfold aPlus crea
  rw [cplxO_neg_left, hn, dRho_cj_neg hψ, dRho_cj_neg hψ]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, map_mul, map_sub, map_neg,
    map_inv₀, Complex.conj_ofReal, Complex.conj_I]
  ring

end GlobalTheory.FockConjNeg

namespace GlobalTheory.FockConjNeg

variable {D : D7}

theorem fock_true_eq_ptF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.Grid.fock ψ θ true S T f P = ptF ψ θ (frSgn true (Fr.ofModel S.M)) (Fr.ofModel T.M) f P := by
  have hc : (frSgn true (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => cart_frSgn true (Fr.ofModel S.M) τ
  unfold ptF
  rw [hc]
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem cj_ptF_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} (A : Fr V) (B : Fr W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ (GlobalTheory.Grid.neg V) W f)
    (P : PolF D W.rank V.rank) :
    cj id (ptF ψ θ (frSgn true A) B f P) = ptF ψ θ A B (cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have hcf : IsThetaFunO ψ V W (cj id f) := GlobalTheory.CjNeg.theta_negS' hψ hf
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, ← mul_one (MvPolynomial.C a), ← mul_one (MvPolynomial.C (starRingEnd ℂ a)),
      GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one, GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | add p q hp hq =>
    rw [map_add, GlobalTheory.FockAdjoint.ptF_add, GlobalTheory.FockAdjoint.ptF_add, ← hp, ← hq]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.map_X, mul_comm, GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ (frSgn true A) B hf, mul_comm,
      GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ A B hcf, ← hp, cart_frSgn]
    exact aPlus_cj_neg hψ hθ (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn true A) B hf p) v.1 _ _ _

theorem fock_neg_cj : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  intro D S T ψ θ f hψ hθ hf P
  rw [fock_true_eq_ptF, cj_ptF_neg hψ hθ _ _ hf]
  rfl

end GlobalTheory.FockConjNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainTw.ParInv

variable {D : D7}

theorem conjP_eq_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl', GlobalTheory.GridPlaces.under_conjP]

theorem absNorm_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem conjPl_ne_of_isSplit (w : HeightOneSpectrum (𝓞 D.host.E))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : Formalism.DivisionValues.conjPl w ≠ w := by
  rintro hc
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) R.asIdeal = (w.under (𝓞 D.host.F)).asIdeal → R = w := by
    intro R hR
    rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (HeightOneSpectrum.ext hR) with h | h
    · exact h
    · rw [h, conjP_eq_conjPl', hc]
  exact hPQ ((key P hP).trans (key Q hQ).symm)

end GlobalTheory.ChainTw.ParInv

end

open GlobalTheory.ChainTw.ParInv in

theorem GlobalTheory.ChainTw.invFam_bounded : ∀ D : D7, ForStageQ D fun c _ j s => ∀ (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E), IsPar u (chainPar c B j) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.ChainNS.invFam B) D.R.r ((D.R.r : ℝ) / 2) := by
  intro D c tw htw j hj s hs u B hu hB
  classical
  obtain ⟨hr, -, hflat⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hflat.selfDual
  obtain ⟨hu0, hpar⟩ := hu
  obtain ⟨v0, hv0⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (Subtype.ext (LinearMap.ext fun v => by simpa using h v))
  have hP := hpar v0 hv0
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram s.V
  have key : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hw
    have hd :=
      (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) hJ.2 hsd.1).2 (fun y => hsd.2 y) (w.under (𝓞 D.host.F))
    have hx := hP (w.under (𝓞 D.host.F)) hv w rfl
    by_cases hc : Formalism.DivisionValues.conjPl w = w
    · rw [hc]
      rcases hx with ⟨hs, -⟩ | ⟨hin, -⟩
      · exact absurd hc (conjPl_ne_of_isSplit w hs)
      · exact (GlobalTheory.LFun.ConjPlace.map_inv_of_isParamVec hin (hP _ hv w rfl)).symm
    · have hx' := hP (w.under (𝓞 D.host.F)) hv (Formalism.DivisionValues.conjPl w) (under_conjPl w)
      exact GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd (Ne.symm hc) hx hx'
  intro w hw
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    show (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [under_conjPl]; exact hw
  have hB' : B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv D c htw.com j hj B w hw (key w hw)
  have e : GlobalTheory.ChainNS.invFam B w = B (Formalism.DivisionValues.conjPl w) := hB'.symm
  rw [e]
  have h2 := hB (Formalism.DivisionValues.conjPl w) hw'
  rwa [absNorm_conjPl'] at h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_avg_type_other_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @GlobalTheory.AvgOtherPlace.isTypeAt_avgN | exact GlobalTheory.AvgOtherPlace.isTypeAt_avgN | (intros; apply GlobalTheory.AvgOtherPlace.isTypeAt_avgN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteAvgApprox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal

namespace GlobalTheory.KFinCuspApprox

theorem approx_one_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  intro hP D θ hθ N φ hφ τ a δ hδ
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 a
  have hr := rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc
  have hη : 0 < δ / ((C : ℝ) + 1) := div_pos hδ (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.KAvgApprox.one_place D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) φ hr d _ hη
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hav := GlobalTheory.KAvgApprox.avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) e hec φ hr
  set ψ : GA D N.V → ℂ := φ - avgN θ N τ e φ with hψ
  have hψr : RapidDecSm θ N.V ψ := by
    have := hr.add (hav.smul (-1))
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψc : IsCuspFun N.V ψ := by
    have h2 := GlobalTheory.T.cusp_form_avg_is_cusp θ hθ hP N τ e hec φ hA hc
    have := GlobalTheory.MultMem.isCuspFun_add hr.toIsAutFun (hav.smul (-1)).toIsAutFun hc (GlobalTheory.MultMem.isCuspFun_smul (-1) h2)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := by
    intro k hk hk' x
    simp only [hψ, Pi.sub_apply, hlev k hk hk' x]
    congr 1
    show (∫ k', e k' * φ (x * k * _) ∂_) = ∫ k', e k' * φ (x * _) ∂_
    congr 1; funext k'
    rw [mul_assoc, ← Formalism.IndefR.Eqv.Act.comm_inf_fin (Formalism.IndefR.Eqv.Act.atTau_mem θ τ _) hk', ← mul_assoc, hlev k hk hk']
  refine ⟨e, hec, he, fun g => ?_⟩
  have h1 := hC ψ hψr.toIsAutFun hψlev hψr.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hψr) hψc
  have h2 : decaySize N.V a ψ ≤ ENNReal.ofReal δ := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (δ / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ a) ≤ ENNReal.ofReal δ :=
    (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ a)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at h3
  simpa [hψ] using h3

end GlobalTheory.KFinCuspApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspValueType

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dRep_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (X : Mx n) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [GlobalTheory.SmVecModel.exp_smul_conj hP]

theorem foldr_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (l : List (Mx n)) (w : H) :
    l.foldr (dRep fun g => σ (P * g * P⁻¹)) w = (l.map fun X => P * X * P⁻¹).foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih, dRep_conj σ hP]

theorem sobNorm_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) S w = sobNorm σ (S.map fun l => l.map fun X => P * X * P⁻¹) w := by
  unfold sobNorm
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, foldr_conj σ hP]

theorem sobNorm_conj_back (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) (S.map fun l => l.map fun X => P⁻¹ * X * P) w = sobNorm σ S w := by
  rw [sobNorm_conj σ hP, List.map_map]
  congr 1
  refine (List.map_congr_left fun l _ => ?_).trans (List.map_id S)
  show List.map (fun X => P * X * P⁻¹) (List.map (fun X => P⁻¹ * X * P) l) = l
  rw [List.map_map]
  refine (List.map_congr_left fun X _ => ?_).trans (List.map_id l)
  exact GlobalTheory.SmVecModel.conj_cancel hP X

theorem exists_ctrl_conj [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) (S₀ : List (List (Mx n))) (hS₀ : Words (lieOf G) S₀) :
    ∃ S, Words (lieOf G) S ∧ Ctrl (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) S ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ w, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) w →
        sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by
  obtain ⟨S₁, hS₁, -, ⟨B, hB, hc⟩, A, hA, hd⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ
    (S₀.map fun l => l.map fun X => P * X * P⁻¹) (by
      intro l hl X hX
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.SmVecModel.lie_conj hP hG (hS₀ l' hl' Y hY))
  refine ⟨S₁.map fun l => l.map fun X => P⁻¹ * X * P, ?_,
    ⟨fun g => B (P * g * P⁻¹), hB.comp (by fun_prop), fun g hg w hw => ?_⟩, A, hA, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact GlobalTheory.SmVecModel.lie_conj_inv hP hG (hS₁ l' hl' Y hY)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj_back σ hP]
    exact hc _ (GlobalTheory.TypeAtCompare.conj_mem hP hG hg) w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj σ hP]
    exact hd w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)

theorem smoothVec_zero (Lie : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) : SmoothVec Lie σ (0 : H) := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem hasTypeAll_single [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) {u : H} (hu : SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) u)
    {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieOf G) (fun g => σ (P * g * P⁻¹)) ℓ) {f : Mx n → ℂ}
    (hf : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ℓ (σ (P * g * P⁻¹) u) = f g) :
    HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) f := by
  obtain ⟨S₀, C₀, hS₀, hb⟩ := hℓ
  obtain ⟨S, hS, hc, A, hA, hd⟩ := exists_ctrl_conj hσ hP hG S₀ hS₀
  have hv : ∀ i, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) ((Pi.single 0 u : ℕ → H) i) := fun i => by
    by_cases hi : i = 0
    · subst hi; simpa using hu
    · rw [Pi.single_eq_of_ne hi]; exact smoothVec_zero _ _
  refine ⟨S, hS, hc, Pi.single 0 u, fun i => if i = 0 then ℓ else 0, Pi.single 0 (|C₀| * A),
    ⟨⟨hv, fun i => ?_, fun i w hw => ?_, ?_, fun g hg => ?_⟩, fun S' _ => ?_⟩⟩
  · by_cases hi : i = 0
    · subst hi; simp only [Pi.single_eq_same]; positivity
    · rw [Pi.single_eq_of_ne hi]
  · by_cases hi : i = 0
    · subst hi
      simp only [if_true, Pi.single_eq_same]
      have h1 := hb w hw
      have h2 := hd w hw
      have h3 : 0 ≤ sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := sobNorm_nonneg _ _ _
      have h4 : C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h3
      calc ‖ℓ w‖ ≤ C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h1
        _ ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h4
        _ ≤ |C₀| * (A * sobNorm (fun g => σ (P * g * P⁻¹)) S w) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |C₀| * A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by ring
    · simp [hi, Pi.single_eq_of_ne hi]
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]
  · rw [← hf g hg]
    have := hasSum_single (f := fun i : ℕ => (if i = 0 then ℓ else 0) (σ (P * g * P⁻¹) ((Pi.single 0 u : ℕ → H) i))) 0
      fun i hi => by simp [hi]
    simpa using this
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]

end Model

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

theorem isTypeAt_value {D : D7} (θ : InfFam D)
    (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec) (τ : D.what₂.Tau) :
    IsTypeAt θ V τ (Sp τ) (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  refine ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, hD, M.fr_unit τ, M.fr_gram τ, fun x => ?_⟩
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  have hall : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ))
      (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (fun g => T v (x * atTau θ V τ g)) := by
    refine hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
    have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
    have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
    show ℓ (M.rep τ g (v τ)) = _
    rw [h2, h1]
    rfl
  exact hasTypeAll_iff.1 hall

end GlobalTheory.CuspValueType

theorem GlobalTheory.CuspValueType.hasTypeAt_cusp : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ hθ N hN F hF w τ
  have hgood : GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) :=
    ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ),
      GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hN (tauE D τ))⟩
  have key : ∀ T, Mult.IsMultMap θ N.M ∅ 1 T → ∀ v, T v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := fun T hT v =>
    GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ (N.S τ) (T v) hP.discreteSeriesUpqExists
      (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
      hP.casselmanWallach hθ hN hgood (hT.aut v)
      (GlobalTheory.CuspValueType.isTypeAt_value θ hP.harishChandraModules N.M hT v τ)
  have main : ∀ T ∈ Mult.Mult θ N.M ∅ 1, ∀ w, PiTensorProduct.lift T w ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, PiTensorProduct.lift.tprod]
        exact Submodule.smul_mem _ r (key T hT v)
      | add a b ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    | zero =>
      intro w
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      intro w
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (ha w) (hb w)
    | smul c a _ ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (ha w)
  have hF' := (Mult.mem_multT θ N.M ∅ 1 F).1 hF
  have eF : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [eF]
  exact main _ hF' w

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def idemAt (w : Pl D.host.E) : AE D := Classical.epsilon fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w

open Classical in

def detIdl (e : AE D) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  if he : e * e = e then GlobalTheory.VecInv.detAt e he V g else 1

open Classical in

theorem detIdl_val {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detIdl e V g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := by
  rw [detIdl, dif_pos he]; rfl

def splitScal (G : GridData L sc) (p : Pair T) (w : Pl D.host.E) (g : GA D (G.pS p)) (h : GA D (G.pT p)) : ℂ :=
  ((splitFacO (G.chrS p) (G.chrT p) (detIdl (idemAt w) (G.pS p) g) (detIdl (idemAt w) (G.pT p) h) : Circle) : ℂ)

end GlobalTheory.RowVacScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  first | exact @GlobalTheory.GridJoin.exists_cosData_agree | exact GlobalTheory.GridJoin.exists_cosData_agree | (intros; apply GlobalTheory.GridJoin.exists_cosData_agree <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatKernelPairingRationalPointsInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerRat

theorem flat_kernel_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ h
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  have hΞ : IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := by
    have e := (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x hx 0
      (s.om (1, h) Φ) (s.weil.om_pres (1, h) Φ hΦ)).2
    simp only [flFB, flatS, hxe]
    exact e
  generalize flFB s (s.om (1, h) Φ) = Ξ at hΞ ⊢
  set Y : GA D J.W₀ → WO J.W₀ B.L → ℂ := fun h₀ => omz (h₀, 1) Φ₀ with hYdef
  have hYl : ∀ γ ∈ GQ J.W₀, ∀ h₀ w, Y (γ * h₀) w = Y h₀ (w ⬝ mt J.W₀ γ) := by
    intro γ hγ h₀ w
    have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀ γ hγ 1 (one_mem _) h₀ 1 w
    rw [one_mul, inv_one, mt_one, Matrix.one_mul] at e
    exact e
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ₀
  have hYc : Continuous fun p : GA D J.W₀ × WO J.W₀ B.L => Y p.1 p.2 :=
    hJ.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  have hn : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
    have h1 : ‖ψ x‖ = 1 := s.weil₀.std.1.2.1 x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  set K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.A → ℂ := fun w p =>
    s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ w) * star (Y p.1 w) with hK
  have hP : ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ) (omz (h₀, 1) Φ₀) 0 =
      ∫ w in vL.𝓕, K w (h₀, h₁) ∂vL.μ := fun h₀ h₁ => by
    simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK, hYdef]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ _ _ _ s.weil₀ Ξ hΞ
    have h2 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        (((q.2.1, B.o.emb (q.2.2, 1)), B.o.jB ⬝ q.1) : (GA D J.W₀ × GA D B.V₀) × WO J.W₀ B.V₀) :=
      ((continuous_fst.comp continuous_snd).prodMk (B.o.continuous_emb.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_const))).prodMk
        (continuous_const.matrix_mul continuous_fst)
    have h3 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        ((q.2.1, q.1) : GA D J.W₀ × WO J.W₀ B.L) := (continuous_fst.comp continuous_snd).prodMk continuous_fst
    exact (h1.comp h2).mul (hYc.comp h3).star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ x p, K (γ + x) p = K x p := by
    rintro _ ⟨γ, rfl⟩ x p
    have e1 := (s.weil₀.om_pres (p.1, B.o.emb (p.2, 1)) Ξ hΞ).quasi (B.o.iB * γ) (B.o.jB ⬝ x)
    have e2 := (homz.om_pres (p.1, 1) Φ₀ hΦ₀).quasi γ x
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x) = symplOH J.W₀ B.L (rat γ) x := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ (rat γ + x)) * star (omz (p.1, 1) Φ₀ (rat γ + x)) =
      s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ x) * star (omz (p.1, 1) Φ₀ x)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, -, -, hinv⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  refine ⟨fun γ hγ h₀ h₁ => ?_, fun γ hγ h₀ h₁ => ?_⟩
  · rw [hP, hP, ← hinv (GlobalTheory.PairKer.mulRight J.W₀ _ γ) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) ?_ (h₀, h₁)]
    · congr 1; funext w
      have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ s.weil₀ Ξ hΞ γ hγ 1 (one_mem _) h₀ (B.o.emb (h₁, 1)) (B.o.jB ⬝ w)
      rw [one_mul, inv_one, mt_one, Matrix.one_mul, Matrix.mul_assoc] at e
      change s.om₀ (γ * h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ w) * star (Y (γ * h₀) w) =
        s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ (w ⬝ mt J.W₀ γ)) * star (Y h₀ (w ⬝ mt J.W₀ γ))
      rw [e, hYl γ hγ]
    · intro x
      refine ⟨fun h => ?_, fun h => ratMx_mul h ((mem_GQ_iff _ _).1 hγ)⟩
      rw [← (GlobalTheory.PairKer.mulRight J.W₀ _ γ).symm_apply_apply x]
      exact ratMx_mul h ((mem_GQ_iff _ _).1 (inv_mem hγ))
  · refine (hP h₀ (γ * h₁)).trans (Eq.trans ?_ (hP h₀ h₁).symm)
    refine integral_congr_ae (.of_forall fun w => ?_)
    have e := GlobalTheory.PairKer.om_emb s.weil₀ hΞ B.o hγ h₀ h₁ w
    show K w (h₀, γ * h₁) = K w (h₀, h₁)
    rw [hK]
    exact congrArg (· * star (Y h₀ w)) e

end GlobalTheory.KerRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockNegSubst

open MvPolynomial

theorem map_conj_substF {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.CompactHowe.substF h g P) =
      GlobalTheory.CompactHowe.substF (fun τ => (h τ).map (starRingEnd ℂ)) (fun τ => (g τ).map (starRingEnd ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [GlobalTheory.CompactHowe.substF, MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, RingHom.id_apply]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul (GlobalTheory.CompactHowe.substF h g), map_mul (MvPolynomial.map (starRingEnd ℂ)), hp,
      map_mul (MvPolynomial.map (starRingEnd ℂ)), map_mul, MvPolynomial.map_X, GlobalTheory.CompactHowe.substF_X,
      GlobalTheory.CompactHowe.substF_X]
    congr 1
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

theorem map_conj_conj {σ : Type} (P : MvPolynomial σ ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => Complex.conj_conj z
  rw [e, MvPolynomial.map_id]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_map_conj {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (MvPolynomial.map (starRingEnd ℂ) Q) =
      fun x => starRingEnd ℂ (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT
        (fun w => starRingEnd ℂ (f w)) Q x) := by
  funext x
  induction Q using MvPolynomial.induction_on' with
  | monomial k a =>
    have hm := GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f hψ hθ k x
    have e1 : (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) =
        (starRingEnd ℂ a) • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, e1, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ← hm]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hp, hq, map_add]

end GlobalTheory.FockNegSubst

namespace GlobalTheory.FockNegSubst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT v : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ), IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f P = pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (v τ).map (starRingEnd ℂ)) (fun τ => (((u τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T hψ hθ BS u BT v f hf P
  have hf' : IsThetaFunO ψ S T (fun w => starRingEnd ℂ (f w)) := GlobalTheory.CjNeg.theta_negS' hψ hf
  rw [← map_conj_conj P,
    pureTensorO_negSp_map_conj ψ θ S T hψ hθ (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f
      (MvPolynomial.map (starRingEnd ℂ) P),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS u BT v _ hf' (MvPolynomial.map (starRingEnd ℂ) P),
    ← map_conj_substF, pureTensorO_negSp_map_conj ψ θ S T hψ hθ BS BT f]

end GlobalTheory.FockNegSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgCol

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frRel (W : G.Weil) {U : Set T} (N : Std G U) (X : Node) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  (W.onb X τ)⁻¹ * N.frC X τ

def frCh (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => frRel W N (.top (j + 1)) τ) (fun τ => ((frRel W N (.top j) τ)⁻¹)ᵀ)

def frChInv (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => (frRel W N (.top (j + 1)) τ)⁻¹) (fun τ => (frRel W N (.top j) τ)ᵀ)

end GlobalTheory.AvgCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRealVec

theorem compAt_central {D : D7} {θ : InfFam D} (τ : D.what₂.Tau) {n : ℕ} (c : AE D) :
    ∃ s : ℂ, compAt θ τ (c • (1 : Matrix (Fin n) (Fin n) (AE D))) = s • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨θ τ (infPart D c), ?_⟩
  ext i j
  by_cases h : i = j
  · subst h; simp [compAt]
  · simp [compAt, h]

theorem vec_theta_fock : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} {N : GlobalTheory.FunObj.Std G U} (Z : GlobalTheory.FunObj.Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, GlobalTheory.FunObj.DefPair D.R.m p → ∀ d : GlobalTheory.FunObj.FinDatum G t p, Z.HasVec d → IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) (Z.vec d) := by
  intro D T L sc G W U N Z t p hp d hv
  obtain ⟨f, hf⟩ := hv
  have hvac := Z.vac_is p hp
  have hψ := hvac.1
  have hV := hvac.2
  have hθ : IsInfFam W.θ := hV.inf
  have hf0 := hV.theta
  have hft : IsThetaFunO W.ψ (G.pS p) (G.pT p) f := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ hf hf0
  have he : infPart D d.e = 0 := GlobalTheory.PlaceVec.idemSum_infPart d.e_is
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ
      (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ he (GlobalTheory.PlaceVec.infPart_cA he) hf hf0 hft (hV.fock τ)
  have hr : Pair.InRange D.R.m p := by
    have := (DefPair.nodes hp).2
    unfold Pair.InRange
    revert this
    cases p.big <;> simp [DefNode, Node.InRange] <;> omega
  have hW := W.om_is p hr
  have hvec : Z.vec d = W.om p (d.z, 1) f := FinDatum.vec_eq W hf
  rw [hvec]
  refine ⟨hW.om_pres _ _ hft, fun τ z => ?_⟩
  obtain ⟨c, hc⟩ := d.z_cen
  obtain ⟨s, hs⟩ := compAt_central (θ := W.θ) τ (n := (G.pS p).rank) c
  have hS : G.cartS W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) * G.cartS W.cart p τ := by
    rw [hc, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hc1 : Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p)) = (1 : AE D) • (1 : Matrix _ _ (AE D)) := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨s', hs'⟩ := compAt_central (θ := W.θ) τ (n := (G.pT p).rank) (1 : AE D)
  have hT : G.onT W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * G.onT W.cart p τ := by
    rw [hc1, hs', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT p).rank) (Fin (G.pS p).rank) ℂ,
      z = compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * z₀ *
        compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z⁻¹) := by
    refine ⟨compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))⁻¹) * z *
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om p (d.z, 1)) (hfock τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW hθ d.z 1 τ hS hT z₀ hft, map_zero] at h0
  exact h0

end GlobalTheory.FockRealVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTerms
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem cabs_gen_le_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) ≤ (Ideal.absNorm P : ℝ) ^ i := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  obtain ⟨g, Λ, Λ', Fd, Fd', h, u, u', v, c1, c2, f1, f2, hh, u0, u0', up, up', m1, m1', hpt⟩ :=
    GlobalTheory.T.heckeIsogeny_generatorRatio_pointwise_bound E H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hz hb hx hx'
  exact_mod_cast GlobalTheory.T.periodic_theta_norm_mean_factor_le g Λ Λ' Fd Fd' h u u' p _ v _ c1 c2 f1 f2 hA.2.2.1.pos hh u0 u0' up up' m1 m1' hpt

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivRealLineEqSumRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

namespace GlobalTheory.PlaceSum
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem hD_finset_sum {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) {α : Type} (s : Finset α)
    (u : α → R) : hD ι π om (∑ a ∈ s, u a) f = ∑ a ∈ s, hD ι π om (u a) f := by
  funext w
  rw [Finset.sum_apply]
  simp only [hD_eq_fderiv ι π om f hf, map_sum, ContinuousLinearMap.sum_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem deriv_heisO_eq_sum_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  intro D ψ hψ θ hθ S T f hf L hLc hLf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e1 : (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f :=
    dLine_eq_hD h hψ (L := L) ⟨hLc, hLf⟩ f
  have e2 : ∀ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1)) f := by
    intro τ
    have hl := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ (L 1))
    rw [dRho_eq_dLine]
    exact dLine_eq_hD h hψ ⟨hl.1, hl.2.1⟩ f
  have e3 : piW θ T S (L 1) = ∑ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) := by
    funext τ' i j
    simp only [Finset.sum_apply]
    have hc : ∀ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) τ' i j =
        compAt θ τ' (lineAt θ τ (compAt θ τ (L 1)) 1) i j := fun τ => rfl
    simp only [hc]
    rw [Finset.sum_eq_single τ']
    · rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ' (compAt θ τ' (L 1))).2.2 1 τ', if_pos rfl, Complex.ofReal_one,
        one_smul]
      rfl
    · intro b _ hb
      rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ b (compAt θ b (L 1))).2.2 1 τ', if_neg (Ne.symm hb)]
      rfl
    · intro hn; exact absurd (Finset.mem_univ τ') hn
  rw [e1, e3, hD_finset_sum _ _ _ f (theta_sm h hf)]
  exact Finset.sum_congr rfl fun τ _ => (e2 τ).symm

end GlobalTheory.PlaceSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumUniq

theorem idemSum_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  intro D P e e' h h'
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ PP PP (hes PP hP) (hes' PP hP)).1 rfl

end GlobalTheory.IdemSumUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefStep

variable {D : D7}

def finOf (V : HSp D) (g : GA D V) : GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2

def infOf (V : HSp D) (g : GA D V) : GinfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).1

theorem infOf_mul_finOf (V : HSp D) (g : GA D V) : ((infOf V g : GinfC V) : GA D V) * (finOf V g : GA D V) = g :=
  (GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g

def IsFinReal {V : HSp D} {Wsp : Type} [AddCommGroup Wsp] [Module ℂ Wsp] (ρ : GA D V →* Module.End ℂ Wsp)
    (F : GA D V → ℂ) (Λ : Module.Dual ℂ Wsp) (v : GfC V → Wsp) : Prop :=
  ∀ g, F g = Λ (ρ g⁻¹ (v (finOf V g)))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frGL (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (τ : D.what₂.Tau) : GL (Fin (G.V X).rank) ℂ :=
  Formalism.UG.bc (tauE D τ) (fr X)

def realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* (D.what₂.Tau → GL (Fin (G.V X).rank) ℂ) :=
  MonoidHom.pi fun τ ↦ (MulAut.conj (frGL fr X τ)⁻¹).toMonoidHom.comp
    ((Pi.evalMonoidHom (fun _ : D.what₂.Tau ↦ GL (Fin (G.V X).rank) ℂ) τ).comp (GlobalTheory.CoefModel.realGL θ (G.V X)))

def realAct (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* Module.End ℂ (VV ℂ (wt G X)) :=
  (rhoK (wt G X)).comp (invTrK.comp (realIn θ fr X))

theorem realAct_fin (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) {g : GA D (G.V X)}
    (hg : g ∈ GfC (G.V X)) : realAct θ fr X g = 1 := by
  have h : GlobalTheory.CoefModel.realGL θ (G.V X) g = 1 := by
    funext τ
    show Formalism.UG.bc (θ τ) (infHom (G.V X) g) = 1
    rw [show infHom (G.V X) g = 1 from hg, map_one]
  have h2 : realIn θ fr X g = 1 := by
    funext τ
    simp [realIn, h]
  rw [realAct, MonoidHom.comp_apply, MonoidHom.comp_apply, h2, map_one, map_one]

end GlobalTheory.DefStep

namespace GlobalTheory.DefStep
variable {D : D7}

theorem split_symm_eq (V : HSp D) {g : GA D V} (a : GinfC V) (b : GfC V) (h : (a : GA D V) * b = g) :
    (GlobalTheory.AdelicSplit.splitEquiv V).symm g = (a, b) :=
  (GlobalTheory.AdelicSplit.splitEquiv V).symm_apply_eq.2 h.symm

theorem finOf_fin (V : HSp D) (b : GfC V) : finOf V b = b := by
  rw [finOf, split_symm_eq V 1 b (one_mul _)]

theorem finOf_mul_inf (V : HSp D) (g : GA D V) (k : GinfC V) : finOf V (g * k) = finOf V g := by
  have h : ((infOf V g * k : GinfC V) : GA D V) * (finOf V g : GA D V) = g * k := by
    have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC V k.2 (finOf V g).2
    conv_rhs => rw [← infOf_mul_finOf V g]
    rw [Subgroup.coe_mul, mul_assoc, hc, ← mul_assoc]
  rw [finOf, split_symm_eq V _ _ h]

theorem finOf_mul_fin (V : HSp D) (g : GA D V) (k : GfC V) : finOf V (g * k) = finOf V g * k := by
  have h : ((infOf V g : GinfC V) : GA D V) * ((finOf V g * k : GfC V) : GA D V) = g * k := by
    rw [Subgroup.coe_mul, ← mul_assoc, infOf_mul_finOf]
  rw [finOf, split_symm_eq V _ _ h]

end GlobalTheory.DefStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_partialSums_bounded_compact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  first | exact @GlobalTheory.PoinAut.partialSum_bdd | exact GlobalTheory.PoinAut.partialSum_bdd | (intros; apply GlobalTheory.PoinAut.partialSum_bdd <;> assumption)
end


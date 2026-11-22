import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLeviMatrixActionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMean
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSqInt

theorem thetaO_norm_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  intro D ψ hψ S T μ 𝓕 hC F hF
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hO : OpensMeasurableSpace (WO S T) := BorelSpace.opensMeasurable
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ w
    obtain ⟨ξ, rfl⟩ := hγ
    have hq := hF.quasi ξ w
    have e : ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ratW T S ξ := rfl
    rw [e, hq, norm_mul, hn, one_mul]
  · obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hF
    have hle : ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _x in 𝓕, ENNReal.ofReal M ^ 2 ∂μ := by
      refine lintegral_mono fun x => ?_
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM x)
    rw [setLIntegral_const, hC.2.2, mul_one] at hle
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle
  · have h1 : ∀ x, F x * starRingEnd ℂ (F x) = (((‖F x‖ ^ 2 : ℝ)) : ℂ) := fun x => by
      rw [Complex.mul_conj']; push_cast; rfl
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg ‖F x‖)
      ((hF.cont.norm.pow 2).measurable.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

end GlobalTheory.ThetaSqInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (χS χT : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)), Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω → ∀ φ : WO (Vc D i) (Wc D i) → ℂ, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ (h : GA D (Vc D i)) (γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → ∀ g : GA D (Wc D i), Datum.thetaKO ω h (γ * g) φ = Datum.thetaKO ω h g φ := by
  first | exact @GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary | exact GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary | (intros; apply GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivial
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffVanish

theorem matrixCoeff_eq_zero : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν →
    ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 →
      ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'

  obtain ⟨U₁, hU₁, hGfix⟩ := hG.level
  obtain ⟨U₂, hU₂, hG'fix⟩ := hG'.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro ξ u hu hfin hψu
  obtain ⟨hcomp, -, hkeep, hunit, -⟩ := GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ
  have hGu : heisO ψ V W u G = G := hGfix u hu.1 hfin
  have hG'u : heisO ψ V W u G' = G' := hG'fix u hu.2 hfin

  have hswap : symplOH V W u ξ = -symplOH V W ξ u := GlobalTheory.MixModel.symplOH_skew V W ξ u
  have hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G := by
    have hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G := by
      have h := hcomp ξ u G
      rwa [hGu] at h
    rw [hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hswap, GlobalTheory.ThetaSquare.symplO_eq]
    ring

  set c : ℂ := ψ (-symplO V W ξ u) with hc
  have hI := hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'
  rw [hmove, hG'u] at hI
  unfold GlobalTheory.Ker.ipO at hI
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI
  rw [MeasureTheory.integral_const_mul] at hI
  have hc1 : c ≠ 1 := by
    intro h1
    apply hψu
    have hprod : ψ (symplO V W ξ u) * c = 1 := by
      rw [hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rwa [h1, mul_one] at hprod
  have hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end GlobalTheory.CoeffVanish

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {D : D7}

theorem omO_of_single (V W : HSp D) (τ : D.what₂.Tau) (x y : GlobalTheory.FockCompare.RW W V) (hy : ∀ b, b ≠ τ → y b = 0) :
    GlobalTheory.OrientedHeis.omO V W y x = GlobalTheory.OrientedHeis.formAt V W τ (y τ) (x τ) := by
  show ∑ b, GlobalTheory.OrientedHeis.formAt V W b (y b) (x b) = _
  refine Finset.sum_eq_single τ (fun b _ hb => ?_) (by simp)
  rw [hy b hb]
  simp [GlobalTheory.OrientedHeis.formAt]

theorem omO_piW_lineAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (V W : HSp D) (ξ : WO V W) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    GlobalTheory.OrientedHeis.omO V W (GlobalTheory.FockCompare.piW θ W V ξ) (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ z 1)) =
      -symplAt V W τ z (compAt θ τ ξ) := by
  have skew : ∀ x y, GlobalTheory.OrientedHeis.omO V W x y = -GlobalTheory.OrientedHeis.omO V W y x := fun x y => by
    have e := GlobalTheory.OrientedHeis.omO_self (S := V) (T := W) h (x + y)
    simp only [map_add, LinearMap.add_apply, GlobalTheory.OrientedHeis.omO_self h] at e
    linarith
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt h.inf (m := W.rank) (n := V.rank) τ z
  have hc : ∀ b, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ z 1) b = compAt θ b (lineAt θ τ z 1) := fun b => rfl
  rw [skew, omO_of_single V W τ _ _ (fun b hb => by rw [hc, hL.2.2 1 b, if_neg hb]; rfl), hc, hL.2.2 1 τ, if_pos rfl,
    Complex.ofReal_one, one_smul]
  exact congrArg Neg.neg (GlobalTheory.OrientedRealForm.formAt_eq V W τ z (compAt θ τ ξ))

theorem psi_symplOH_lineAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) (V W : HSp D) (ξ : WO V W) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (t : ℝ) :
    ψ (symplOH V W ξ (lineAt θ τ z t)) =
      Complex.exp ((Real.pi * Complex.I) * ((t * symplAt V W τ z (compAt θ τ ξ) : ℝ) : ℂ)) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines D θ σ h W V).2.1 _
    (GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ z) t
  rw [e, GlobalTheory.OrientedHeis.psi_symplOH h hψ, LinearMap.map_smul, smul_eq_mul, omO_piW_lineAt h]
  congr 1
  push_cast
  ring

theorem dRho_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (ξ : WO V W) {H : WO V W → ℂ}
    (hH : IsThetaFunO ψ V W H) :
    dRho (heisO ψ V W) θ τ z (heisO ψ V W ξ H) =
      heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z H) +
        (-(2 * Real.pi * Complex.I) * (symplAt V W τ z (compAt θ τ ξ) : ℂ)) • heisO ψ V W ξ H := by
  have hA := (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ
  have hU := hA.2.1
  have hDS := ((hA.2.2 θ hθ).1 τ z).1 H hH
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set a := symplAt V W τ z (compAt θ τ ξ) with ha
  set c : ℂ := -(2 * Real.pi * Complex.I) * (a : ℂ) with hc
  funext x
  let g : ℝ → ℂ := fun t => heisO ψ V W ξ (heisO ψ V W (lineAt θ τ z t) H) x
  have hfun : (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) (heisO ψ V W ξ H) x) =
      fun t : ℝ => Complex.exp (c * (t : ℂ)) * g t := by
    funext t
    simp only [g]
    rw [hU.1 (lineAt θ τ z t) ξ H, hU.1 ξ (lineAt θ τ z t) H, add_comm (lineAt θ τ z t) ξ, skew ξ,
      Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, AddChar.map_neg_eq_inv,
      psi_symplOH_lineAt hψ hθ V W ξ τ z t, ← Complex.exp_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hc]
    push_cast
    ring
  have hg : HasDerivAt g (ψ (symplOH V W x ξ) * dRho (heisO ψ V W) θ τ z H (x + ξ)) 0 :=
    (hDS (x + ξ)).const_mul _
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * ((0 : ℝ) : ℂ)) * (c * 1)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul c).cexp
  have hg0 : g 0 = heisO ψ V W ξ H x := by
    simp only [g, map_zero]
    unfold heisO
    rw [GlobalTheory.ThetaSquare.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  show deriv (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) (heisO ψ V W ξ H) x) 0 = _
  rw [hfun]
  refine (hexp.mul hg).deriv.trans ?_
  rw [hg0]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  show _ = ψ (symplOH V W x ξ) * dRho (heisO ψ V W) θ τ z H (x + ξ) + _
  ring

theorem pow_bound {X F : Type*} (P : F → Prop) (Dop : F → F) (B : X → F → F → ℂ) (a : X → ℝ)
    (hD : ∀ G, P G → P (Dop G)) (h0 : ∀ G G', P G → P G' → ∃ C : ℝ, ∀ ξ, ‖B ξ G G'‖ ≤ C)
    (h1 : ∀ ξ G G', P G → P G' → |a ξ| * ‖B ξ G G'‖ ≤ ‖B ξ G (Dop G')‖ + ‖B ξ (Dop G) G'‖) :
    ∀ (m : ℕ) (G G' : F), P G → P G' → ∃ C : ℝ, ∀ ξ, |a ξ| ^ m * ‖B ξ G G'‖ ≤ C := by
  intro m
  induction m with
  | zero =>
    intro G G' hG hG'
    obtain ⟨C, hC⟩ := h0 G G' hG hG'
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  | succ m ih =>
    intro G G' hG hG'
    obtain ⟨C₁, hC₁⟩ := ih G (Dop G') hG (hD _ hG')
    obtain ⟨C₂, hC₂⟩ := ih (Dop G) G' (hD _ hG) hG'
    refine ⟨C₁ + C₂, fun ξ => ?_⟩
    calc |a ξ| ^ (m + 1) * ‖B ξ G G'‖ = |a ξ| ^ m * (|a ξ| * ‖B ξ G G'‖) := by ring
      _ ≤ |a ξ| ^ m * (‖B ξ G (Dop G')‖ + ‖B ξ (Dop G) G'‖) :=
        mul_le_mul_of_nonneg_left (h1 ξ G G' hG hG') (by positivity)
      _ = |a ξ| ^ m * ‖B ξ G (Dop G')‖ + |a ξ| ^ m * ‖B ξ (Dop G) G'‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add (hC₁ ξ) (hC₂ ξ)

theorem norm_coef_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {ν : Measure (WO V W)} {𝓕 : Set (WO V W)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (ξ : WO V W) {G G' : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (hG' : IsThetaFunO ψ V W G') :
    |symplAt V W τ z (compAt θ τ ξ)| * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤
      ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (dRho (heisO ψ V W) θ τ z G' x) ∂ν‖ +
        ‖∫ x in 𝓕, heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G) x * star (G' x) ∂ν‖ := by
  have hA := (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ
  have hU := hA.2.1
  have hDS := (hA.2.2 θ hθ).1 τ z
  have hDG := hDS.2.1 G hG
  have e := hDS.2.2 ν 𝓕 hν h𝓕 (heisO ψ V W ξ G) G' (hU.2.2.1 ξ G hG) hG'
  rw [dRho_heisO hψ hθ τ z ξ hG] at e
  set a := symplAt V W τ z (compAt θ τ ξ) with ha
  set c : ℂ := -(2 * Real.pi * Complex.I) * (a : ℂ) with hc
  have hI1 := GlobalTheory.Size.integrableOn_mul_conj hψ hν h𝓕 (hU.2.2.1 ξ _ hDG) hG'
  have hI2 := GlobalTheory.Size.integrableOn_mul_conj hψ hν h𝓕 (hU.2.2.1 ξ _ hG) hG'
  have hsplit : GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G) + c • heisO ψ V W ξ G) G' =
      GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G' + c * GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G' := by
    unfold GlobalTheory.Ker.ipO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_add hI1 (hI2.const_mul c), integral_const_mul]
  rw [hsplit] at e
  have e2 : c * GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G' =
      -GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) (dRho (heisO ψ V W) θ τ z G') -
        GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G' := by
    linear_combination e
  have hn : ‖c‖ = 2 * Real.pi * |a| := by
    rw [hc, norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have h3 : ‖c‖ * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ ≤
      ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) (dRho (heisO ψ V W) θ τ z G')‖ +
        ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G'‖ := by
    rw [← norm_mul, e2, sub_eq_add_neg, ← neg_add]
    rw [norm_neg]
    exact norm_add_le _ _
  have h4 : |a| * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ ≤ ‖c‖ * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ := by
    rw [hn]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h0 : 0 ≤ |a| * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ := by positivity
    nlinarith
  exact h4.trans h3

theorem norm_coef_bdd {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {ν : Measure (WO V W)} {𝓕 : Set (WO V W)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) {G G' : WO V W → ℂ} (hG : IsThetaFunO ψ V W G)
    (hG' : IsThetaFunO ψ V W G') :
    ∃ C : ℝ, ∀ ξ : WO V W, ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  have hSI := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1
  obtain ⟨a, ha⟩ := (hSI G hG).2.1
  obtain ⟨b, hb⟩ := (hSI G' hG').2.1
  have hfin : ν 𝓕 < ⊤ := lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hν h𝓕).2
  refine ⟨a * b * (ν 𝓕).toReal, fun ξ => ?_⟩
  refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
  rw [norm_mul, norm_star, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0))

theorem coef_decay : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∀ θ : InfFam D, IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ ξ : WO V W, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ ξ)| ^ m * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
  have hDS := (((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).2.2 θ hθ).1 τ z
  exact pow_bound (IsThetaFunO ψ V W) (dRho (heisO ψ V W) θ τ z)
    (fun ξ F F' => ∫ x in 𝓕, heisO ψ V W ξ F x * star (F' x) ∂ν) (fun ξ => symplAt V W τ z (compAt θ τ ξ))
    (fun F hF => hDS.2.1 F hF) (fun F F' hF hF' => norm_coef_bdd hψ hν h𝓕 hF hF')
    (fun ξ F F' hF hF' => norm_coef_le hψ hθ hν h𝓕 τ z ξ hF hF') m G G' hG hG'

end GlobalTheory.ThetaDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffSmearContinuousPeriodicFubini
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanSmear

theorem exists_bound {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : ∃ C, ∀ u, ‖G u‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.cont.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨γ, hγm, hγ⟩ := hcov u
  obtain ⟨γ0, rfl⟩ := hγm
  have e : ((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl
  have h1 := hC _ hγ
  rw [e, hG.quasi, norm_mul, hψ.1.2.1, one_mul] at h1
  exact h1

theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
  unfold GlobalTheory.IsoMean.emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end GlobalTheory.IsoMeanSmear

namespace GlobalTheory.IsoMeanSmear

theorem smear : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun u => ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∧ (∀ γ ∈ ratL W V, ∀ u, ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G (γ + u) * star (G' (γ + u)) ∂μ = ∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∧ ∀ φ : WO V W → ℂ, Continuous φ → (∀ u, ‖φ u‖ ≤ 1) → ∫ ξ in 𝓨, (∫ u in 𝓕, φ u * (heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) ∂ν) ∂μ = ∫ u in 𝓕, φ u * (∫ ξ in 𝓨, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u) ∂μ) ∂ν := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨hHaar, -, h1⟩ := hμ
  obtain ⟨-, -, s1, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨-, -, s2, -, -, K, hK, hcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI := s1
  haveI := s2
  haveI : FirstCountableTopology (WO V W) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology (WO V W)
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI hfμ : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : Countable D.host.E := by
    haveI : FiniteDimensional ℚ D.host.E := inferInstance
    exact (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin V.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin V.rank → D.host.E))
  haveI : Countable (ratL W V) := (Set.countable_range _).to_subtype
  have hνF : ν 𝓕 < ⊤ := by
    have hcov' : ∀ x : WO V W, ∃ γ ∈ ratL W V, γ + x ∈ K := hcov
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov' ν h𝓕
  haveI hfν : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hνF⟩
  haveI : SFinite (ν.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfν)
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfμ)
  obtain ⟨C, hC⟩ := exists_bound hψ hG
  obtain ⟨C', hC'⟩ := exists_bound hψ hG'
  set Φ : Mx D a b × WO V W → ℂ := fun p => heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q p.1) G p.2 * star (G' p.2) with hΦ
  have he := continuous_emb V W P Q
  have hcont : Continuous Φ := by
    simp only [hΦ, heisO]
    exact ((hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd (he.comp continuous_fst))).mul
      (hG.cont.comp (continuous_snd.add (he.comp continuous_fst)))).mul (hG'.cont.comp continuous_snd).star
  have hbd : ∀ p, ‖Φ p‖ ≤ C * C' := by
    intro p
    simp only [hΦ, heisO, norm_mul, norm_star, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg _).trans (hC 0))
  refine ⟨?_, ?_, ?_⟩
  · refine continuous_of_dominated (bound := fun _ => C * C') (fun u => ?_) (fun u => ?_) (integrable_const _) ?_
    · have hu : Continuous fun ξ => Φ (ξ, u) := hcont.comp (continuous_id.prodMk continuous_const)
      exact hu.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => hbd (ξ, u)
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have hξ : Continuous fun u => Φ (ξ, u) := hcont.comp (continuous_const.prodMk continuous_id)
      exact hξ
  · intro γ hγ u
    obtain ⟨γ0, rfl⟩ := hγ
    have er : ((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ0 = ratW W V γ0 := rfl
    rw [er]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hH := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hG (GlobalTheory.IsoMean.emb V W P Q ξ)
    simp only
    rw [hH.quasi, hG'.quasi, star_mul]
    have hn : ψ (-(symplOH V W (ratW W V γ0) u)) * star (ψ (-(symplOH V W (ratW W V γ0) u))) = 1 := by
      have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ0) u))
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
      norm_num
    linear_combination (heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q ξ) G u * star (G' u)) * hn
  · intro φ hφ hφ1
    have hint : Integrable (Function.uncurry fun ξ u => φ u * Φ (ξ, u)) ((μ.restrict 𝓨).prod (ν.restrict 𝓕)) := by
      refine Integrable.of_bound ?_ (C * C') (Filter.Eventually.of_forall fun p => ?_)
      · exact ((hφ.comp continuous_snd).mul hcont).aestronglyMeasurable
      · simp only [Function.uncurry, norm_mul]
        calc ‖φ p.2‖ * ‖Φ (p.1, p.2)‖ ≤ 1 * (C * C') :=
              mul_le_mul (hφ1 _) (hbd _) (norm_nonneg _) zero_le_one
          _ = C * C' := one_mul _
    refine (integral_integral_swap hint).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact integral_const_mul _ _

end GlobalTheory.IsoMeanSmear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeries
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScalingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_invariant_rationalLeviScaling : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.LeviRes.res_levi | exact GlobalTheory.LeviRes.res_levi | (intros; apply GlobalTheory.LeviRes.res_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionIsotropicSplitSmoothRealPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_isotropicSplit_smooth_realPoints : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO V' W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => res V V' W C B μ 𝓨 f (w + L t) := by
  first | exact @GlobalTheory.TowerSmooth.res_smooth | exact GlobalTheory.TowerSmooth.res_smooth | (intros; apply GlobalTheory.TowerSmooth.res_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLeviMatrixActionIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_levi_matrix_action_identity : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ a : GA D V, HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) → ∀ g : GA D V, HMul.hMul ((matHom V g).1 - 1) (C.map (incA D)) = 0 → HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D)) ((matHom V g).1 - 1) = 0 → (∀ x : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec x = 0 → ∃ y : Fin r → AE D, ((matHom V g).1 - 1).mulVec (fun i => incA D (x i)) = (C.map (incA D)).mulVec y) → ∃ m : GA D V, m ∈ NI V C ∧ g = a * m * a⁻¹ * m⁻¹ := by
  first | exact @GlobalTheory.UnipLevi.commutator_levi | exact GlobalTheory.UnipLevi.commutator_levi | (intros; apply GlobalTheory.UnipLevi.commutator_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMeanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadicalMean_eq_volume_mul_rationalMean : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (m : Matrix (Fin s) (Fin r) D.host.E), m.rank = s → ∃ (μ : Measure (Mx D s V'.rank)) (𝓐 : Set (Mx D s V'.rank)), IsCovolOne (ratMx D s V'.rank) μ 𝓐 ∧ ∀ φ : Mx D s V'.rank → ℂ, Continuous φ → (∀ γ ∈ ratMx D s V'.rank, ∀ a, φ (γ + a) = φ a) → ∫ n in 𝓝, φ (HMul.hMul (HMul.hMul ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V (n : GA D V) - 1)) (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  first | exact @GlobalTheory.UnipMean.mean_eq_volume_mul | exact GlobalTheory.UnipMean.mean_eq_volume_mul | (intros; apply GlobalTheory.UnipMean.mean_eq_volume_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_wittEmbedding_le_const_mul : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g := by
  first | exact @GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le | exact GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le | (intros; apply GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le <;> assumption)
end


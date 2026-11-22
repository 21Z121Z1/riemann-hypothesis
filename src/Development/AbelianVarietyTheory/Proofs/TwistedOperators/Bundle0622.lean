import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0580
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitaryPoint_mem_heckeClosure : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal →
    ϖ ∉ P.asIdeal ^ 2 → ∀ h ∈ GfC V, Formalism.L2.Theta.SuppAt e V h →
      h ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) := by
  first | exact @GlobalTheory.SplitCartanGen.supp_mem_closure | exact GlobalTheory.SplitCartanGen.supp_mem_closure | (intros; apply GlobalTheory.SplitCartanGen.supp_mem_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ), IsUnif ϖ → ∀ f : Matrix A B k → ℂ, (∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z) →
    ∀ M : GL A k, M ∈ KO k A →
      ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) = ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  first | exact @GlobalTheory.ResSumInv.sum_res_mul_left | exact GlobalTheory.ResSumInv.sum_res_mul_left | (intros; apply GlobalTheory.ResSumInv.sum_res_mul_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

theorem tame_kills_real_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ →
    ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) →
    ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  intro D ψ θ hψ hθ S T A B ℓ hℓ f hf hP w hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hcont, hsurj, htr⟩ := GlobalTheory.T.fockRealPoint_transport_continuous_integral D θ σ hσ S T A B
  obtain ⟨z₀, rfl⟩ := hsurj w hw
  have hth := hf.1
  set F : VCx D.what₂.Tau S.rank T.rank → ℂ := fun z => ℓ (heisO ψ S T (fockPt σ A B z) f) with hFdef
  have hFc : Continuous F := (hℓ.cont f hth).comp hcont
  obtain ⟨M, hM⟩ := hℓ.bdd f hth
  have hFb : ∃ M : ℝ, ∀ z, ‖F z‖ ≤ M := ⟨M, fun z => hM _⟩
  have key : ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g →
      IsThetaFunO ψ S T (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) →
      ℓ (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = ∫ z, g z * F z := by
    intro g hg hthg
    obtain ⟨m, α, hm, hα, hH⟩ := htr g hg
    have e1 : (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = fun x => ∫ w, α w * heisO ψ S T w f x ∂m := by
      funext x; exact (hH fun w => heisO ψ S T w f x).symm
    rw [e1] at hthg ⊢
    rw [hℓ.sup f hth m α hα hthg]
    exact hH fun w => ℓ (heisO ψ S T w f)
  obtain ⟨C, hC⟩ := ((GlobalTheory.ThetaSquare.squareIntegrable hψ) f hth).2.1
  have hG : ∀ x, ∃ M : ℝ, ∀ z, ‖rd ψ σ A B f x z‖ ≤ M * Real.exp (gq (fw D) z / 2) := by
    intro x
    refine ⟨C, fun z => ?_⟩
    rw [rd, norm_mul, GlobalTheory.ThetaSquare.norm_heisO hψ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have hent := GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf
  have hc : ∀ τ, 0 < fw D τ := fw_pos D
  obtain ⟨hint1, hint2⟩ := GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian D.what₂.Tau S.rank T.rank (fw D) hc
  have hgq : ∀ z : VCx D.what₂.Tau S.rank T.rank, ∀ x, (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z =
      (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x := by
    intro z x
    rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring

  obtain ⟨Cj, hCj⟩ := GlobalTheory.T.fock_gaussian_jets_at_origin_eq_fock_vectors D ψ θ σ hψ hσ S T A B
  have hpt : ∀ P, IsThetaFunO ψ S T (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    fun P => GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hth P
  have hmom : ∀ m : DVar D.what₂.Tau S.rank T.rank →₀ ℕ,
      ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * F z = 0 := by
    intro m
    set K : ℂ := ((∏ τ, (Real.pi / fw D τ) ^ (S.rank * T.rank) : ℝ) : ℂ) *
      ((m.prod fun k n => (fw D k.1)⁻¹ ^ n : ℝ) : ℂ) with hK
    have e : (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
        (K * Cj m) • GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) := by
      funext x
      have h1 := GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) m
      rw [hCj f hf x m] at h1
      have h2 : (fun z => conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
          fun z => conjMono m z * (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z := by
        funext z; rw [mul_assoc, mul_assoc, hgq]
      rw [h2, h1, Pi.smul_apply, smul_eq_mul]
      ring
    have hthe : IsThetaFunO ψ S T (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) *
        heisO ψ S T (fockPt σ A B z) f x) := by
      rw [e]
      exact GlobalTheory.OrientedHeis.theta_smul _ (hpt _)
    have := key _ (hint1 m) hthe
    rw [← this, e, hℓ.smul _ _ (hpt _), hP, mul_zero]

  have hU := GlobalTheory.T.integral_exp_bk_mul_eq_zero_of_moments_zero D.what₂.Tau S.rank T.rank (fw D) hc F hFc hFb hmom z₀
  set K' : ℂ := ((∏ τ, (fw D τ / Real.pi) ^ (S.rank * T.rank) : ℝ) : ℂ) * (Real.exp (-gq (fw D) z₀ / 2) : ℂ) with hK'
  have e : (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) = heisO ψ S T (fockPt σ A B z₀) f := by
    funext x
    have h1 := GlobalTheory.T.fock_bargmann_reproducing_formula D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) z₀
    have h2 : heisO ψ S T (fockPt σ A B z₀) f x = (Real.exp (-gq (fw D) z₀ / 2) : ℂ) * rd ψ σ A B f x z₀ := by
      rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      rw [show -gq (fw D) z₀ / 2 + gq (fw D) z₀ / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [h2, h1]
    have h3 : (fun z => (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
        heisO ψ S T (fockPt σ A B z) f x) = fun z => K' * (Complex.exp (bk (fw D) z₀ z) *
          ((Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z)) := by
      funext z; rw [hgq]; ring
    rw [h3, integral_const_mul, hK']
    simp only [mul_assoc]
    ring
  have hthe : IsThetaFunO ψ S T (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) := by
    rw [e]; exact (GlobalTheory.ThetaSquare.heisUnitary hψ).2.2.1 _ _ hth
  have := key _ ((hint2 z₀).const_mul K') hthe
  rw [e] at this
  change ℓ (heisO ψ S T (fockPt σ A B z₀) f) = 0
  rw [this]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp_rw [← mul_assoc] at hU ⊢
  rw [hU, mul_zero]

end GlobalTheory.FockTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  first | exact @GlobalTheory.RowEx.dat_choice_exists | exact GlobalTheory.RowEx.dat_choice_exists | (intros; apply GlobalTheory.RowEx.dat_choice_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem chrS_top_prod_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}, L.Is μ₀ →
    ∀ (j : ℕ), j + 1 < D.R.m → ∀ y : ∀ w : locPl G t, (Kw w.1)ˣ,
    ((G.chrS (.top t j) (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (y w) : ℂˣ) : ℂ) := by
  intro D T L sc G t μ₀ hL j hj y
  have hrank : (G.pS (.top t j)).rank = rankX D j :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).rank
  have hchr : G.chrS (.top t j) = L.mu t (j + 1) := by
    rw [GridData.chrS, hrank]
    simp [Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D j)]
  have hE : ChrEq (L.mu t (j + 1)) (muBase L (j + 1) * L.xiH t) := by
    have h1 : muBase L (j + 1) = L.C.mu0 ⟨j, by omega⟩ := dif_pos (by omega)
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, by omega⟩) (hL.xi t)
  rw [hchr, map_prod]
  rw [show ∀ (s : Finset (locPl G t)) (f : locPl G t → Circle), ((∏ w ∈ s, f w : Circle) : ℂ) = ∏ w ∈ s, (f w : ℂ) from
    fun s f => map_prod Circle.coeHom f s]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact congrArg (fun f => ((f (y w) : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedConjugateFixesStandardVacuumTopPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
noncomputable section

namespace GlobalTheory.TopLevelInv

section Unr

variable {D : D7}

theorem unrOff_mul' {e : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ)
    (h' : Formalism.IndefR.Fin.UnrOff e χ') : Formalism.IndefR.Fin.UnrOff e (χ * χ') :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem unrOff_inv' {e : AE D} {χ : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ) :
    Formalism.IndefR.Fin.UnrOff e χ⁻¹ :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

theorem pg_near_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    {PP : Pl D.host.E} (h : PP ∈ L.Pg) : ∃ w ∈ locPl G t, PP = w ∨ PP = GlobalTheory.IdemSupport.cP w := by
  classical
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  have hm := GlobalTheory.LevelRamif.typePrime_mem hk
  set v := PP.under (𝓞 D.host.F) with hv
  have hvk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  have hS1 : v ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  have hS0 : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
  refine ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hS0), ?_⟩
  exact GlobalTheory.IdemSupport.eq_or_eq_cP (by rw [G.pl.under_w hS0])

theorem conjPrime_conjPrime₂ (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO])

theorem unrOff_mu_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}
    (hL : L.Is μ₀) (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) ∧ Formalism.IndefR.Fin.UnrOff e L.eta := by
  classical
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t j
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.mu0 j) he fun PP' h1 h2 => by
      refine h4 PP' (fun h => ?_) fun PP h h' => ?_
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        rcases hw' with rfl | rfl
        · exact h1 hw
        · exact h2 w hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        have e1 := (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h'
        rcases hw' with rfl | rfl
        · exact h2 PP hw h'
        · rw [conjPrime_conjPrime₂] at e1
          exact h1 (e1 ▸ hw)
  have hxi : Formalism.IndefR.Fin.UnrOff e (L.xi t) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.xi t) he fun PP' h1 h2 => by
      by_contra hn
      rcases (hL.Q_ram t PP').1 hn with h | ⟨PP, h, h'⟩
      · exact h1 (Finset.mem_union_right _ h)
      · exact h2 PP (Finset.mem_union_right _ h) h'
  exact ⟨unrOff_mul' hmu hxi, GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e hL.eta he fun PP' _ _ => L.C.isEta.unr PP'⟩

end Unr

set_option maxHeartbeats 1000000 in

theorem vacFix_conjPt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ e : AE D, IsIdemSum e (locPl G t) → ∀ ε : AF D.host.F, IsIdempotentElem ε →
    algebraMap (AF D.host.F) (AE D) ε = e + cA D e →
    W.om (.top t j) (1, resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) (S.Z.vac (.top t j)) =
      S.Z.vac (.top t j) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he ε hε halg
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hdS : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hdT : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hS := S.N.selfDual (X := .top j) hdS
  have hT := S.N.selfDual (X := .top (j + 1)) hdT
  have hfS := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top j))) (G.Λ (.top j)) (S.βp j)
    (Lev.finE (G.V (.top j)) (S.N.u (.top j)).1) (S.βp_is j hdS) (S.N.u_lat _ hdS)
  have hfT := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdT) (S.N.u_lat _ hdT)
  have hrkS : (G.V (.top j)).rank = rankX D j := (G.isV (X := .top j) hdS fun _ e => by cases e).rank
  have hrkT : (G.V (.top (j + 1))).rank = rankX D (j + 1) := (G.isV (X := .top (j + 1)) hdT fun _ e => by cases e).rank
  have hrk : (G.V (.top j)).rank ≠ (G.V (.top (j + 1))).rank := by
    intro h
    rw [hrkS, hrkT] at h
    simp only [rankX, add_mul, one_mul] at h
    omega
  have hev : Even (G.V (.top j)).rank := hrkS ▸ even_rankX D j
  obtain ⟨hμ, hη⟩ := unrOff_mu_locPl G hL ⟨j, by omega⟩ he
  have hatt : ∀ n, Formalism.IndefR.Fin.UnrOff e (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) := by
    intro n
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · exact unrOff_mul' hμ (unrOff_inv' hη)
    · exact hμ
  have hn : ∃ (μ : Measure (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (𝓕 : Set (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))),
      IsCovolOne (ratL (G.pT (.top t j : Pair T)) (G.pS (.top t j : Pair T))) μ 𝓕 ∧
        nrm2 μ 𝓕 (S.Z.vac (.top t j)) = 1 := by
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.2.norm
    exact ⟨p.1, p.2, hp, hall p hp⟩

  have hf := GlobalTheory.ExpansionInvariance.idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := GlobalTheory.ExpansionInvariance.idem_compl hf
  have hcut : resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k) =
      GlobalTheory.ExpansionInvariance.cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) (conjPt S j k) := by
    apply Formalism.IndefR.Fin.LevelGroupLemmas.gaExt
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG _ hε', GlobalTheory.ExpansionInvariance.mt_cutPart h2.1 h2.2, map_sub, map_one, halg]
    unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hSt : Lev.finE (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) ∈
      St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
    have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
        (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
    rw [hcut]
    exact GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
      (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) (conjPt S j k)
      (by simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
        have h3 := (Subgroup.mem_inf.1 hk2).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 Q
        rw [Subgroup.mem_iInf] at h4
        exact Subgroup.mem_comap.1 (h4 hQ))
  have hP : ∀ a b, (e + cA D e) * (mt (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) - 1) a b = 0 := by
    intro a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hε' _ a b, ← mul_assoc, map_sub, map_one, halg]
    have h0 : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
      linear_combination (-1 : AE D) * hf.1
    rw [h0, zero_mul]
  exact Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D) W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) hrk (Or.inl hev) _ _ hS hT _ _
    hfS hfT (locPl G t) e he (hatt _) (hatt _) _ hv.2.theta hv.2.lat hn 1 _ (one_mem _)
    (Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC _ hε' (SetLike.coe_mem _)) (by rw [map_one]; exact one_mem _) hSt
    (fun a b => by rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', sub_self, Matrix.zero_apply, mul_zero]) hP

end GlobalTheory.TopLevelInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSubStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace : ∀ {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M) (ρ : ι → M →ₗ[ℂ] M)
    (inv : ι → ι), (∀ x ∈ G, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ G, ρ i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y)) →
    (∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f) →
    ∀ (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M), (∀ x, e x ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G) →
    (∀ x, ∀ f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G, b (e x) f = b x f) →
    ∀ Y : Submodule ℂ M, FiniteDimensional ℂ Y → Y ≤ G → (∀ i, ∀ y ∈ Y, ρ i y ∈ Y) → ∀ x ∈ Y, e x ∈ Y := by
  first | exact @GlobalTheory.KTypeProj.typeSpan_proj_mem | exact GlobalTheory.KTypeProj.typeSpan_proj_mem | (intros; apply GlobalTheory.KTypeProj.typeSpan_proj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingFilledArgsMoveInnerLastColumnVertexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ),
    (∀ l, l ≠ j → l ≠ j + 1 → downMap hs x' e' l = downMap hs x e l) →
    downMap hs x' e' j = (g⁻¹).val * downMap hs x e j →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val →
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) (fill hs x y e) = fill hs x' y e' := by
  first | exact @GlobalTheory.TopLevelInv.fill_moveVertex | exact GlobalTheory.TopLevelInv.fill_moveVertex | (intros; apply GlobalTheory.TopLevelInv.fill_moveVertex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt : ∀ {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}, ChrEq c χ → ∀ (T : Finset (Pl D.host.E)), (∀ P ∈ T, χ.TameAt P) → ∀ (a : ∀ P : Pl D.host.E, (Kw P)ˣ) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → (∀ P ∈ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = (a P : Kw P)) → (∀ P ∉ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = 1) → ((c x : Circle) : ℂ) = ∏ P ∈ T, ((χ.loc P (a P) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame | exact GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame | (intros; apply GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_induction_on_splitPlaceSupport : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  first | exact @GlobalTheory.SplitInduct.induct_suppSplit | exact GlobalTheory.SplitInduct.induct_suppSplit | (intros; apply GlobalTheory.SplitInduct.induct_suppSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLiftStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_split_place_indicator_lift : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact @GlobalTheory.SplitDetChr.alpha_det_eq_one | exact GlobalTheory.SplitDetChr.alpha_det_eq_one | (intros; apply GlobalTheory.SplitDetChr.alpha_det_eq_one <;> assumption)
end


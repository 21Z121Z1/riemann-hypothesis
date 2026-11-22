import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0616
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0611
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_gk_le_multiplicity_span : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ A : Submodule ℂ (GA D V → ℂ), GlobalTheory.CuspGK.IsIrrGKSub θ M A → (∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) →
    A ≤ GlobalTheory.CuspGK.multSpan θ M := by
  first | exact @GlobalTheory.CuspGKId.le_multSpan | exact GlobalTheory.CuspGKId.le_multSpan | (intros; apply GlobalTheory.CuspGKId.le_multSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedUnipotentRadicalAtRealPlaceTrivialAtPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem isClosed_cmp_eq_one {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) :
    IsClosed {p : NI V C | cmp θ τ (p : GA D V) = 1} :=
  isClosed_eq ((GlobalTheory.Cusp.KinfCompact.continuous_realMat hθ V τ).comp continuous_subtype_val)
    continuous_const

theorem isClosed_atP_and_isClosed_offP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), IsClosed (GlobalTheory.FibreAtTau.atP θ V C τ : Set (NI V C)) ∧ IsClosed (GlobalTheory.FibreAtTau.offP θ V C τ : Set (NI V C)) := by
  intro D θ hθ V r C τ
  constructor
  · have e : (atP θ V C τ : Set (NI V C)) = (Subtype.val ⁻¹' (GinfC V : Set (GA D V))) ∩
        ⋂ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), {p : NI V C | cmp θ τ' (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_atP, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    exact ((GlobalTheory.Cusp.KinfCompact.isClosed_realPts V).preimage continuous_subtype_val).inter
      (isClosed_iInter fun τ' => isClosed_iInter fun _ => isClosed_cmp_eq_one hθ V C τ')
  · have e : (offP θ V C τ : Set (NI V C)) = {p : NI V C | cmp θ τ (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_offP, Set.mem_ofPred_eq]
    rw [e]
    exact isClosed_cmp_eq_one hθ V C τ

end GlobalTheory.FibreAtTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGKSubmoduleISupGelfandJointEigenspacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGKSubmodule_iSup_gelfandJointEigenspaces : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  first | exact @GlobalTheory.GKEigen.isGKSub_iSup_eigen | exact GlobalTheory.GKEigen.isGKSub_iSup_eigen | (intros; apply GlobalTheory.GKEigen.isGKSub_iSup_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralInvNegXi0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.StairFrameFJ

private theorem isIntegral_sqrtMinusD' (D : D7) : IsIntegral ℤ D.host.sqrtMinusD := by
  refine IsIntegral.of_pow (n := 2) two_pos ?_
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
    unfold Host.sqrtMinusD
    exact D.host.sqd_sq
  rw [hsq]
  refine IsIntegral.neg ?_
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ)))

theorem isIntegral_inv_neg_xi0 (D : D7) : IsIntegral ℤ (-D.host.xi0)⁻¹ := by

  unfold Host.xi0
  rw [neg_div, neg_neg, one_div, inv_inv]
  refine IsIntegral.mul ?_ (isIntegral_sqrtMinusD' D)
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((Ideal.absNorm D.host.ccK : ℕ) : ℤ)))

private theorem mem_integer_of_isIntegral_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {y : k} (hy : IsIntegral ℤ y) : y ∈ 𝒪[k] := by
  have h2 : IsIntegral 𝒪[k] y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hz ▸ z.2

theorem exists_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : x ≠ 0) (h : IsIntegral ℤ x⁻¹) :
    ∃ u : 𝒪[k], (u : k) * p.pr (incA D x) = 1 := by
  have hy : IsIntegral ℤ (p.pr (incA D x⁻¹)) := h.map ((p.pr.comp (incA D)).toIntAlgHom)
  refine ⟨⟨_, mem_integer_of_isIntegral_int hy⟩, ?_⟩
  show p.pr (incA D x⁻¹) * p.pr (incA D x) = 1
  rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx, map_one, map_one]

theorem exists_frame : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : 𝒪[k]),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (-D.host.xi0)) = 1) ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (star (-D.host.xi0))) = 1) ∧
  Function.Injective j ∧
  (∀ r i, β.b i (j r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) ∧
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) := by
  unfold OnStd All
  intro D hq T L μ₀ hL sc G W M _ F _ σ h' v hv
  obtain ⟨k, _, _, _, _, p, hpv, hpe⟩ := GlobalTheory.LatticeMembershipValuation.exists_splitPoint_at_S0 G.pl hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨β, j, hβ, hj, hcol, horth⟩ := GlobalTheory.LatticeMembershipValuation.exists_stairFrame (p := p) hq hL G hv (2 * σ + 2) (by omega) h'
    hpv hpe hϖ
  have hx0 : D.host.xi0 ≠ 0 := by
    exact GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hs : IsIntegral ℤ (star (-D.host.xi0))⁻¹ := by
    have h1 : IsIntegral ℤ (star (-D.host.xi0)⁻¹) :=
      (isIntegral_inv_neg_xi0 D).map ((starRingEnd D.host.E).toIntAlgHom)
    rwa [star_inv₀] at h1
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β, j, ϖ, hpv, hpe, hβ,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    exists_inv p (neg_ne_zero.2 hx0) (isIntegral_inv_neg_xi0 D),
    exists_inv p (star_ne_zero.2 (neg_ne_zero.2 hx0)) hs, hj, hcol, ?_⟩
  intro m hm r
  have hmr := horth m hm r
  have hf : (fun x => p.pr (incA D x)) = ⇑(p.pr.comp (incA D)) := rfl
  rw [hf, Matrix.map_mul, Matrix.mul_assoc] at hmr
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply] using hmr

end GlobalTheory.StairFrameFJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAverageHasTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K_average_has_type : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  exact @GlobalTheory.PlaceDecomp.hasCtp_kAvg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LagrangianDecompositionWeil
section
open ValuativeRel

noncomputable section
namespace GlobalTheory.SvNAnyChar

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  let ψ1 : AddChar k ℂ := ψ0.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψ1 : ∀ t, ψ1 t = ψ0 (c * t) := fun t => rfl
  have hψ1c : Continuous ψ1 := by
    have e : (ψ1 : k → ℂ) = fun t => ψ0 (c * t) := funext hψ1
    rw [e]; exact hψ.comp (continuous_const.mul continuous_id)
  have hcond : ∀ x : k, (∀ y ∈ 𝒪[k], ψ1 (x * y) = 1) ↔ x ∈ 𝒪[k] := fun x => by
    simp only [hψ1]; exact hc x
  let S : (κ → k) × (κ → k) →+ (κ → k) × (κ → k) :=
    AddMonoidHom.prodMap (AddMonoidHom.id _) (DistribMulAction.toAddMonoidHom _ c⁻¹)
  have hS : ∀ w, S w = (w.1, c⁻¹ • w.2) := fun w => rfl
  let mc : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k := DistribMulAction.toAddMonoidHom _ c
  let wT' := S.comp wT
  let wM' := (S.comp wM).comp mc
  have hT' : ∀ Y, wT' Y = ((wT Y).1, c⁻¹ • (wT Y).2) := fun Y => rfl
  have hM' : ∀ z, wM' z = ((wM (c • z)).1, c⁻¹ • (wM (c • z)).2) := fun z => rfl
  have hschr : ∀ w (φ : (κ → k) → ℂ), GlobalTheory.WeilM.schr ψ0 w φ = GlobalTheory.WeilM.schr ψ1 (S w) φ := by
    intro w φ; funext x
    simp only [GlobalTheory.WeilM.schr, hS, hψ1, dotProduct_smul, smul_eq_mul]
    congr 2
    field_simp
  obtain ⟨ι, hbij, htr, hmul⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians ψ1 hψ1c hcond wT' wM'
    (fun Y Y' => by
      have e := hT Y Y'
      simp only [hT', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, mul_zero])
    (fun z z' => by
      have e := hM (c • z) (c • z')
      simp only [hM', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, mul_zero])
    (fun Y z => by
      have e := hTM Y (c • z)
      simp only [hT', hM', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp)
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (w.1, c • w.2)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      show S (wT Y) + S (wM (c • c⁻¹ • z)) = w
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, ← map_add, h, hS]
      simp [smul_smul, inv_mul_cancel₀ hc0])
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · rw [hschr]; exact htr Y φ hφ
  · have e : S (wM z) = wM' (c⁻¹ • z) := by
      show S (wM z) = S (wM (c • c⁻¹ • z))
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [hschr, e, hmul _ φ hφ]
    funext Y'
    congr 1
    rw [hψ1]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.SvNAnyChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnArrowRealAverageFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.LastColAvg

theorem exps_chi : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ (a b : D.what₂.Tau → ℚ) (e₁ e₂ : D.what₂.Tau → ℤ),
      (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) ∧ (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) ∧
      (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) ∧
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) := by
  intro D T L sc G μ0 hL i hi
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have hatt : ∀ (n : ℕ) τ, HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
    intro n τ
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · rw [sub_eq_add_neg]
      exact GlobalTheory.Chain.StepVac.hasInfExp_mul (h0 τ) (GlobalTheory.Chain.StepVac.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
    · simpa using h0 τ
  refine ⟨fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0,
    fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0,
    fun τ => (cen D sc.cGap τ (D.R.m - i) : ℤ) - (((G.pS (.chi i D.R.m : Pair T)).rank + 1) / 2 : ℕ),
    fun τ => ((((G.pT (.chi i D.R.m : Pair T)).rank + 1) / 2 : ℕ) : ℤ) - (cen D sc.cGap τ (D.R.m - i) : ℤ),
    fun τ => hatt _ τ, fun τ => hatt _ τ, fun τ => ?_, fun τ => ?_⟩
  · simp only [sgnP]
    rcases Nat.even_or_odd (G.pS (.chi i D.R.m : Pair T)).rank with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
      push_cast; ring
    · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast; ring
  · simp only [sgnP]
    rcases Nat.even_or_odd (G.pT (.chi i D.R.m : Pair T)).rank with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
      push_cast; ring
    · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      push_cast; ring

theorem ker_fock_moved_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m → ∀ (t : T), t ∈ U → ∀ (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    ∀ (P : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (x : GA D (G.V (.grid i D.R.m))) (y : GA D (G.V (.grid (i + 1) D.R.m))),
    W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S d) P) x y =
      W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (S.Z.vec d) P) (x * (S.N.u (.grid i D.R.m)).1) (y * (S.N.u (.grid (i + 1) D.R.m)).1) := by
  intro D T L sc G W U S μ0 hL i hi t ht d hd P x y
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi i D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, -⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have m1 : (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1).1 ∈
      GfC (G.pS (.chi i D.R.m : Pair T)) := negGA_mem_GfC _ (S.N.u _).2
  have m2 : (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1).2 ∈
      GfC (G.pT (.chi i D.R.m : Pair T)) := (S.N.u _).2
  have e : W.fock (.chi i D.R.m) (movedVec t S d) P =
      W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1)
        (W.fock (.chi i D.R.m) (S.Z.vec d) P) :=
    (GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ _ hom W.θ W.θ_is _ m1 _ m2 _ _ _ _ (S.Z.vec d) P h1).symm
  rw [e]
  unfold GridData.Weil.ker
  rw [GlobalTheory.RowClaim.toPair_mul]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem real_average : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank)
      (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))), ∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.grid i D.R.m))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.grid i D.R.m)) (h : GA D (G.V (.grid (i + 1) D.R.m))) (v : VV ℂ (wt G (.grid i D.R.m))),
        ∫ k, W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
            ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h *
            Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹
            (fockComp W S.N.frC (.chi i D.R.m : Pair T) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL i hi Q Λ
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := exps_chi G hL i hi
  obtain ⟨σ₀, hσf, hσr⟩ := GlobalTheory.T.exists_fockFrameChange_lastColumn_definitePair S hL i hi
  obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactPair_realAverage_fock_eq_jetOperator S hL i hi a b ha hb e₁ e₂ he₁ he₂ (σ₀ Q) Λ
  refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hh : h = ((finOf _ h : GfC (G.V (.grid (i + 1) D.R.m))) : GA D (G.V (.grid (i + 1) D.R.m))) *
      ((infOf _ h : GinfC (G.V (.grid (i + 1) D.R.m))) : GA D (G.V (.grid (i + 1) D.R.m))) := by
    rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (infOf _ h).2 (finOf _ h).2, infOf_mul_finOf]
  let ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ :=
    ((LinearMap.proj 0 : (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
      W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) ((x * S.N.u _ : FinPt G (.grid i D.R.m)) : GA D (G.V (.grid i D.R.m)))
        ((finOf _ h * S.N.u _ : FinPt G (.grid (i + 1) D.R.m)) : GA D (G.V (.grid (i + 1) D.R.m))))) ∘ₗ
      fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d)
  have key : ∀ k : GinfC (G.V (.grid i D.R.m)),
      W.kerA (.right i D.R.m : Arrow T) (W.fock (.chi i D.R.m) (movedVec t S d) Q)
        ((x : GA D (G.V (.grid i D.R.m))) * (k : GA D (G.V (.grid i D.R.m)))) h =
      realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) (infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))) *
        ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) (infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))) (σ₀ Q)) := by
    intro k
    show W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S d) Q) _ _ = _
    conv_lhs => rw [hh]
    rw [ker_fock_moved_real hL W S t hp d hd a b ha hb e₁ e₂ he₁ he₂ _ k.2 _ (infOf _ h).2 Q _ _,
      ker_fock_moved_fin S hL i hi t ht d hd, hσf t ht d hd, hσr _ k.2 _ (infOf _ h).2]
    rfl
  simp_rw [key]
  rw [hΛ' ℓ κ hκ hκp _ (infOf _ h).2 v]
  have hY : realAct W.θ S.N.fr (.grid (i + 1) D.R.m) h⁻¹ =
      realAct W.θ S.N.fr (.grid (i + 1) D.R.m) ((infOf _ h : GA D (G.V (.grid (i + 1) D.R.m))))⁻¹ := by
    conv_lhs => rw [hh]
    rw [mul_inv_rev, map_mul, realAct_fin _ _ _ (inv_mem (finOf _ h).2), mul_one]
  rw [hY]
  rfl

end GlobalTheory.LastColAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeOf_stabiliser_mul_inv_eq_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ k : FinPt G X,
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X)) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V X) k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X))) →
    GlobalTheory.SumSize.latAt S X (k * (S.N.u X)⁻¹) = stdL D _ := by
  first | exact @GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL | exact GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL | (intros; apply GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftUp_multiplicitySpaces_span_kFiniteVectors : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  first | exact @GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | exact GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | (intros; apply GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span <;> assumption)
end


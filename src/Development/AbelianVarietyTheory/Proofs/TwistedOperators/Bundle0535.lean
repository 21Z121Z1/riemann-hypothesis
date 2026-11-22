import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgOtherPlace

open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem atTau_comm (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) :
    atTau θ V τ g * atTau θ V τ' h = atTau θ V τ' h * atTau θ V τ g := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have a := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  have b := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hh
  refine R.2.2.1 _ (mul_mem a.1 b.1) _ (mul_mem b.1 a.1) fun ρ => ?_
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul]
  by_cases c : ρ = τ
  · subst c
    rw [a.2.1, b.2.2 ρ (Ne.symm hne), Matrix.mul_one, Matrix.one_mul]
  · rw [a.2.2 ρ c, Matrix.mul_one, Matrix.one_mul]

theorem adAt_atTau_of_ne (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    adAt θ (atTau θ V τ g) τ' X = X := by
  have a := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  have b := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hg a
  rw [adAt, a.2.2 τ' hne, b.2.2 τ' hne, Matrix.one_mul, Matrix.mul_one]

section Avg

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}

variable (θ V) in

def avgF (τ : D.what₂.Tau) (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ) (e : K → ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ

theorem avgF_zero : avgF θ V μ τ κ e 0 = 0 := by
  funext x
  simp [avgF]

theorem avgF_add (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (he : Continuous e) {f g : GA D V → ℂ} (hf : Continuous f) (hg : Continuous g) :
    avgF θ V μ τ κ e (f + g) = avgF θ V μ τ κ e f + avgF θ V μ τ κ e g := by
  funext x
  simp only [avgF, Pi.add_apply, mul_add]
  exact integral_add (GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hf x)
    (GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hg x)

theorem avgF_smul (c : ℂ) (f : GA D V → ℂ) : avgF θ V μ τ κ e (c • f) = c • avgF θ V μ τ κ e f := by
  funext x
  simp only [avgF, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

theorem avgF_Rder (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ') :
    Rder θ V τ' X (avgF θ V μ τ κ e ψ) = avgF θ V μ τ κ e (Rder θ V τ' X ψ) := by
  set 𝒟 : Set (GA D V → ℂ) := {ψ | IsAutFunSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, IsAutFunSm θ V ψ := fun _ h => h
  have hR : ∀ ψ ∈ 𝒟, ∀ τ'' X, X ∈ lieAt V τ'' → Rder θ V τ'' X ψ ∈ 𝒟 :=
    fun _ h _ _ hX => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX h
  have F := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V K μ (GlobalTheory.RealAverage.famSpan θ V τ κ 𝒟)
    (GlobalTheory.RealAverage.famSpan_cont hθ hκ hU h𝒟) (GlobalTheory.RealAverage.famSpan_sm hθ hU h𝒟)
    (GlobalTheory.RealAverage.famSpan_Rder hθ hκ hU h𝒟 hR)
    (fun k x => e k * ψ (x * atTau θ V τ (κ k))) (Submodule.subset_span ⟨e, he, ψ, hψ, rfl⟩)
  have h1 := F.2.2.1 [(τ', X)] (by simpa using hX)
  simp only [List.foldr_cons, List.foldr_nil] at h1
  show Rder θ V τ' X (fun x => ∫ k, e k * ψ (x * atTau θ V τ (κ k)) ∂μ) = _
  rw [h1]
  funext x
  simp only [avgF]
  congr 1
  funext k
  have e1 : (fun x => e k * ψ (x * atTau θ V τ (κ k))) = e k • rTr V (atTau θ V τ (κ k)) ψ := rfl
  rw [e1, Rder_smul, Rder_rTr hθ (isRealPt_atTau hθ τ (hU k)) hX, adAt_atTau_of_ne hθ hne (hU k)]
  rfl

theorem isGKMap_avgF (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool} {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} {T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)} (hT : IsGKMap θ V τ' ε σ P T) :
    ∃ T' : kFin ε σ →ₗ[ℂ] (GA D V → ℂ), IsGKMap θ V τ' ε σ P T' ∧ ∀ v, T' v = avgF θ V μ τ κ e (T v) := by
  let T' : kFin ε σ →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun v => avgF θ V μ τ κ e (T v)
      map_add' := fun a b => by
        rw [map_add]
        exact avgF_add μ hθ hκ hU he (hT.aut a).cont (hT.aut b).cont
      map_smul' := fun c a => by
        rw [map_smul]
        exact avgF_smul μ c (T a) }
  refine ⟨T', ⟨fun v => ?_, fun g hg hgK v w hw => ?_, fun X hX v w hd => ?_⟩, fun v => rfl⟩
  · exact GlobalTheory.RealAverage.isAutFunSm_average D θ hθ V τ K μ κ hκ hU e he _ (hT.aut v)
  · show avgF θ V μ τ κ e (T w) = rTr V (atTau θ V τ' g) (avgF θ V μ τ κ e (T v))
    rw [hT.mapK g hg hgK v w hw]
    funext x
    simp only [avgF, rTr]
    congr 1
    funext k
    rw [mul_assoc, mul_assoc, atTau_comm hθ hne (hU k) hg]
  · show avgF θ V μ τ κ e (T w) = Rder θ V τ' X (avgF θ V μ τ κ e (T v))
    rw [hT.mapLie X hX v w hd, avgF_Rder μ hθ hne hκ hU he (hT.aut v) hX]

end Avg

section Closure

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}

theorem hasTypeAt_avgF (hθ : IsInfFam θ) (hne : τ' ≠ τ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (he : Continuous e) {S : SPar} {φ : GA D V → ℂ}
    (hφc : Continuous φ) (h : HasTypeAt θ V τ' S φ) : HasTypeAt θ V τ' S (avgF θ V μ τ κ e φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k => atTau θ V τ (κ k) := GlobalTheory.RealAverage.continuous_atTau hθ hκ hU
  let W' : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | Continuous f ∧ avgF θ V μ τ κ e f ∈ finPartOfType θ V τ' S}
      zero_mem' := ⟨continuous_const, by rw [avgF_zero]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, by
        rw [avgF_add μ hθ hκ hU he ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, by
        rw [avgF_smul]; exact Submodule.smul_mem _ c ha.2⟩ }
  have hle : finPartOfType θ V τ' S ≤ W' := by
    refine sSup_le ?_
    rintro W ⟨H, _, _, σ, lam, ε, P, T, hE, hlam, hD, hP, hJ, hT, rfl⟩ f ⟨v, rfl⟩
    obtain ⟨T', hT', hv⟩ := isGKMap_avgF μ hθ hne hκ hU he hT
    refine ⟨(hT.aut v).cont, ?_⟩
    rw [← hv]
    exact (le_sSup (a := LinearMap.range T') ⟨H, _, _, σ, lam, ε, P, T', hE, hlam, hD, hP, hJ, hT', rfl⟩ :
      _ ≤ finPartOfType θ V τ' S) ⟨v, rfl⟩
  intro C hC δ hδ
  have hI0 : 0 ≤ ∫ k, ‖e k‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  set M : ℝ := (∫ k, ‖e k‖ ∂μ) + 1 with hMdef
  have hM : 0 < M := by linarith
  have hC' : IsCompact ((fun p : GA D V × K => p.1 * atTau θ V τ (κ p.2)) '' (C ×ˢ Set.univ)) :=
    (hC.prod isCompact_univ).image (continuous_fst.mul (hk.comp continuous_snd))
  obtain ⟨ψ, hψ, hap⟩ := h _ hC' (δ / M) (div_pos hδ hM)
  have hψ' := hle hψ
  refine ⟨_, hψ'.2, fun x hx => ?_⟩
  have i1 := GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hφc x
  have i2 := GlobalTheory.RealAverage.integrable_avg μ hθ hκ hU he hψ'.1 x
  simp only [avgF]
  rw [← integral_sub i1 i2]
  have hb : ∀ k, ‖e k * φ (x * atTau θ V τ (κ k)) - e k * ψ (x * atTau θ V τ (κ k))‖ ≤ ‖e k‖ * (δ / M) :=
    fun k => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hap _ ⟨(x, k), ⟨hx, Set.mem_univ _⟩, rfl⟩).le (norm_nonneg _)
  have hie : Integrable (fun k => ‖e k‖) μ :=
    he.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le (hie.mul_const _) (Filter.Eventually.of_forall hb)) ?_
  rw [integral_mul_const]
  have hlt : (∫ k, ‖e k‖ ∂μ) < M := by linarith
  calc (∫ k, ‖e k‖ ∂μ) * (δ / M) < M * (δ / M) := mul_lt_mul_of_pos_right hlt (div_pos hδ hM)
    _ = δ := mul_div_cancel₀ _ hM.ne'

end Closure

theorem isTypeAt_avgN : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N hN τ τ' hne e he _ φ hφ
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have p1 := hPr.discreteSeriesUpqExists
  have p2 := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have p3 := hPr.harishChandraModules
  have p4 := hPr.casselmanWallach
  have hT := GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') φ p1 p2 p3 p4 hθ hN
    (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hφ.1 (hφ.2.2 τ')
  have hA := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (KG (N.M.ε τ)) (muK (N.M.ε τ)) _ hκ hU e he φ hφ.1
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ N.V τ' (N.S τ') _ p1 p2 p3 p4 hθ hN (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hA
    (hasTypeAt_avgF (muK (N.M.ε τ)) hθ hne hκ hU he hφ.1.cont hT)

end GlobalTheory.AvgOtherPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  first | exact @GlobalTheory.AscFinBumpAdj.exists_bump_adj | exact GlobalTheory.AscFinBumpAdj.exists_bump_adj | (intros; apply GlobalTheory.AscFinBumpAdj.exists_bump_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetSameLocalCosetSetsOtherBaseLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_same_localCosetSets_other_baseLattice : ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : GlobalTheory.FunObj.Frames G) (B' : GlobalTheory.FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      GlobalTheory.FunObj.cosetSet t w B' h κ' = GlobalTheory.FunObj.cosetSet t₀ w B h κ := by
  first | exact @GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq | exact GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq | (intros; apply GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_half_lattice_detecting_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  (∃ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ≠ 0) →
  ∃ y : WO (Vc D i) (Wc D i), IsHalf (cA D (cA D e)) y ∧
    (∀ k : WO (Vc D i) (Wc D i), IsHalf (cA D e) k → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) → (∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) = 0) →
      R.ψ (symplO (Vc D i) (Wc D i) k y) = 1) ∧
    R.ψ (symplO (Vc D i) (Wc D i) x y) ≠ 1 := by
  first | exact @GlobalTheory.HalfDuality.exists_dual_half | exact GlobalTheory.HalfDuality.exists_dual_half | (intros; apply GlobalTheory.HalfDuality.exists_dual_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isThetaAt_unique {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f f' : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) (h' : IsThetaAt ψ B hs e Λ c f₀ Φ f') : f = f' := by
  obtain ⟨⟨T, hT⟩, h1⟩ := h
  exact (h1 T hT).trans (h'.2 T hT).symm

theorem exists_cosetVec_of_match {D : D7} {S T : Grid.Node D} {V₁ V₂ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin V₂.rank → D.host.E)}
    {I I' : Ideal (𝓞 D.host.E)} {e : AE D} {ψ ψ' : AddChar (AF D.host.F) ℂ}
    (hS : S.V = V₁) (hT : T.V = V₂) (hΛ₁ : HEq S.Λ Λ₁) (hΛ₂ : HEq T.Λ Λ₂) (hI : I = I') (hψ : ψ = ψ')
    (vac : WO (negSp V₁) V₂ → ℂ) (cv : Cos Λ₁ Λ₂ I' → WO (negSp V₁) V₂ → ℂ)
    (hcv : ∀ κ : Cos Λ₁ Λ₂ I', IsThetaAt ψ (symplO (negSp V₁) V₂) (heisO ψ (negSp V₁) V₂) e
      (latO (negSp V₁) V₂ (Λ₁ : Set _) (Λ₂ : Set _) fun _ => True) 1 vac (cosInd e κ) (cv κ))
    (hA : ∀ c : Grid.Coset S T I, ∃ κ : Cos S.Λ T.Λ I, Grid.cosetInd S T e I c = cosInd e κ)
    (hB : ∀ κ : Cos S.Λ T.Λ I, ∃ c : Grid.Coset S T I, Grid.cosetInd S T e I c = cosInd e κ)
    (f : WO S.V T.V → ℂ) (hf : HEq f vac) :
    ∃ v : Grid.Coset S T I → (WO S.V T.V → ℂ), (∀ c, Grid.IsCosetVec ψ' true S T e I c f (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (cv κ)) ∧ ∀ κ, ∃ c, HEq (v c) (cv κ) := by
  subst hS hT hI hψ
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₂
  obtain rfl := eq_of_heq hf
  choose κ hκ using hA
  refine ⟨fun c => cv (κ c), fun c => ?_, fun c => ⟨κ c, HEq.rfl⟩, fun κ' => ?_⟩
  · show IsThetaAt ψ _ _ e _ 1 f (Grid.cosetInd S T e I c) (cv (κ c))
    rw [hκ c]
    exact hcv (κ c)
  · obtain ⟨c, hc⟩ := hB κ'
    refine ⟨c, heq_of_eq ?_⟩
    have h1 := hcv (κ c)
    have h2 := hcv κ'
    rw [← hκ c, hc] at h1
    exact isThetaAt_unique h1 h2

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isFrame_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hR : GlobalTheory.Hk3.Core R F) {G : GlobalTheory.Grid.GridPre R} (hsp : G.IsSpaces) {i : ℕ} (hi : i ≤ D.R.m) :
    Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
  cases i with
  | zero =>
    obtain ⟨c, hc⟩ := hR.lev.βY 0 (by have := D.R.two_le_m; omega)
    exact hc.1
  | succ k =>
    obtain ⟨c, hc⟩ := (hsp.vert k 0 hi (Nat.zero_le _)).frame
    exact hc.1

theorem exists_cosData_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hR hsc G' W hW G hsp hch hag hcos i hi f hf
  have hA := GlobalTheory.T.homLatticeCosetIndicator_primePowers_integralCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  have hB := GlobalTheory.T.exists_homLatticeCosetIndicator_eq_latticeHomCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  exact exists_cosetVec_of_match (I := G.lvl R) (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).sp
    (hag.vert i 0 hi.le (Nat.zero_le _)).sp (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).lat
    (hag.vert i 0 hi.le (Nat.zero_le _)).lat hag.lvl hW.ψ (W.vac i) (W.cosVec i) (hcos i hi) hA hB f hf

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItPair D := by
  first | exact @GlobalTheory.Chain.ItPairObj.itPair_holds | exact GlobalTheory.Chain.ItPairObj.itPair_holds | (intros; apply GlobalTheory.Chain.ItPairObj.itPair_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_embedding_stabilizer : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (c : ℕ) (ε : D.host.E), ε ≠ 0 → ∀ d : HermitianOrthogonalExtensionData A B c ε, ∃ ι : GA D A →* GA D B, (∀ h, ι h = stabilizerEmbedding d h) ∧ Continuous ι ∧ Function.Injective ι ∧ (∀ h, ι h ∈ GQ B ↔ h ∈ GQ A) ∧ (∀ h, ι h ∈ GfC B ↔ h ∈ GfC A) ∧ (∀ h, ι h ∈ GinfC B ↔ h ∈ GinfC A) ∧ (∀ g, g ∈ ι.range ↔ HMul.hMul (mt B g) (d.a.map (incA D)) = d.a.map (incA D)) ∧ (∀ h, HMul.hMul (mt B (ι h)) ((frameMat B A d.ι).map (incA D)) = HMul.hMul ((frameMat B A d.ι).map (incA D)) (mt A h)) ∧ ∀ τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∃ k' ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), ι (atTau θ A τ k) = atTau θ B τ k' := by
  first | exact @GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_hom_properties | exact GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_hom_properties | (intros; apply GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_hom_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtVMemLevSubVOfLift
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

set_option maxHeartbeats 8000000 in

theorem extV_mem_levSubV_of_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (z : (R.HV i t).H), (∀ (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → ∀ h, R.extV i t z (h * κ) = levChi _ (R.βV i) (flagL (R.datVt i t)) κ • ((((P.chi g0 : ℂˣ) : ℂ))⁻¹ • R.extV i t z h)) → R.extV i t z ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P)) (levChi _ (R.βV i) (RecTie.datVP R i t P)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P z hz k hk g
  have hlift : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t)
      (⟨Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) k), hk.2.2⟩ : P.H).1 k :=
    ⟨hk.1, hk.2.1, rfl⟩
  have h2 := (GlobalTheory.lift_mem_levVP R i t P _ k hlift).2
  rw [hz _ k hlift g, h2, smul_smul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePureDataOfCosetIndicatorExpansionsDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ), {d : PureDat G t | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}.Finite := by
  first | exact @GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth | exact GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth | (intros; apply GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E), ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) → B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by
  first | exact @GlobalTheory.ChainInv.conjPl_inv_of_chainPar | exact GlobalTheory.ChainInv.conjPl_inv_of_chainPar | (intros; apply GlobalTheory.ChainInv.conjPl_inv_of_chainPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowTheta

theorem isThetaFunO_cosVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.cosVec i κ) := by
  obtain ⟨e, -, h⟩ := W.cosVec_is
  exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) (W.vac_is i hi).2.2

theorem isThetaFunO_datum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (ρ : G.RealVec) (Φ : G.Datum) (i : Fin D.R.m) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (isThetaFunO_cosVec W i i.2 (Φ i)) (ρ i)

end GlobalTheory.RowTheta

theorem GlobalTheory.RowTheta.rowDatum_isThetaFunO : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ Φ i =>
    GlobalTheory.RowTheta.isThetaFunO_datum ch.W ch.ρ Φ i⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePathStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (Φ : G.Datum) (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G (oppPath t D.R.m)), GlobalTheory.FlipRun.RepFin B ρ t (oppPath t D.R.m) τ (Tflip W B t Φ) → ∃ τ', GlobalTheory.RowClaim.IsFlipFin t B ρ Φ τ' ∧ GlobalTheory.FlipRun.tensE W (oppPath t D.R.m) Q τ = GlobalTheory.RowClaim.oppTens W t (Q.mapDomain GlobalTheory.FlipRun.toOpp) τ' := by
  first | exact @GlobalTheory.OppConv.flipFin_of_repFin | exact GlobalTheory.OppConv.flipFin_of_repFin | (intros; apply GlobalTheory.OppConv.flipFin_of_repFin <;> assumption)
end


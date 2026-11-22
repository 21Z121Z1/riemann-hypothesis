import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.RowEvalHH in
theorem GlobalTheory.RowEvalHH.conj_eval_mem_HH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c v₀ ht hLM hc hv S hS φ hφ
  classical
  obtain ⟨hDS, -, -, -, -, hloc⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  obtain ⟨hinj, hran⟩ := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
    X.B.e X.B.Re X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => (hDS v).2.2.2) (fun v => (X.low v).1) hloc X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens X.B.tens_spec

  let u : (∀ τ, ↥(Wsub R X c τ)) → X.B.Hs := fun y => tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))
  obtain ⟨f, K, hfe, hfn⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_multilinear_norm_sq R F X h hLev hGrp hMod t c ht S hS
  have hfi := GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner f K hfn
  have hgram : ∀ a b, ⟪evF R X h t c S a, evF R X h t c S b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ := by
    intro a b
    rw [← hfe a, ← hfe b, hfi a b, tensT_inner]
    rfl
  have hdense : Dense (Submodule.span ℂ (Set.range u) : Set X.B.Hs) :=
    GlobalTheory.T.dense_span_tensor_of_dense_subspaces' (tensT X) (Wsub R X c) (tensT_inner X) (tensT_dense X) (Wsub_dense R X c)
  obtain ⟨Aop, hA⟩ := GlobalTheory.T.exists_clm_of_gram_eq_smul' u (evF R X h t c S) K hgram hdense
  have hHom : Aop ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    intro g
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy1, hy2⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_intertwines_realGroup R F X h hLev hGrp hMod hHost hιE t c ht hc S hS g y
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    change Aop (X.B.σs g (u y)) = X.B.R (g, 1) (Aop (u y))
    rw [← hy1]
    change Aop (u y') = _
    rw [hA, hA, hy2]
  have hRe : X.B.Re.comp Aop = Aop := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [hA]
    exact GlobalTheory.T.conj_translatedRowEvaluation_levelProjector_fixed R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  have heHom : Aop ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re :=
    Submodule.mem_map.2 ⟨Aop, hHom, hRe⟩

  let y₀ : ∀ τ, ↥(Wsub R X c τ) := fun τ => ⟨c τ (v₀ τ), Submodule.mem_map_of_mem (v₀ τ).2⟩
  have hu0 : u y₀ = X.B.tens X.B.w := by
    have : (fun τ => ((y₀ τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ))) = fun τ => X.B.w (X.pl.symm τ) := by
      funext τ
      exact hv τ
    change tensT X _ = _
    rw [this, tensT_w]
  have hvec : vecOf R X c y₀ = v₀ := by
    funext τ
    apply Subtype.ext
    exact (c τ).symm_apply_apply (v₀ τ)
  obtain ⟨c', -, hnorm⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  have hunit : ∀ τ, ‖((v₀ τ : (MP R).H τ))‖ = 1 := by
    intro τ
    rw [← (c τ).norm_map, hv τ]
    exact (X.low _).1
  obtain ⟨hmem, -, -⟩ := hnorm v₀ hunit S hS
  have hval : Aop (X.B.tens X.B.w) = star φ := by
    rw [← hu0, hA]
    unfold evF
    rw [hvec, dif_pos hmem]
    congr 1
    exact (Lp.ext (hφ.trans hmem.coeFn_toLp.symm)).symm
  have hmemHH : star φ ∈ Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund X.B.Re X.Rph := by
    rw [← hran]
    exact ⟨⟨Aop, heHom⟩, hval⟩
  exact hmemHH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairXStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  first | exact @GlobalTheory.ArchLineContPairLeft.continuous_apply | exact GlobalTheory.ArchLineContPairLeft.continuous_apply | (intros; apply GlobalTheory.ArchLineContPairLeft.continuous_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLineTripleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedeanWeilOperator_line_triple : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (f : SInf F (Fin a × Fin (a + a'))) (x : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F), Continuous fun t => T t f x := by
  first | exact @GlobalTheory.ArchLineCont.continuous_apply | exact GlobalTheory.ArchLineCont.continuous_apply | (intros; apply GlobalTheory.ArchLineCont.continuous_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittTowerRestrictionWeilCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrictChar

theorem continuous_char : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → Continuous c := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ c hc
  obtain ⟨_, _, _, hg4, _⟩ := Formalism.IndefR.Eqv.ga_facts D W
  have hres := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  obtain ⟨f₀, hf₀, hne⟩ := hres.2
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  set g := GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f₀ with hgdef
  have hg : IsThetaFunO ψ V' W g := (hres.1 f₀ hf₀).2.1
  have hcont1 : Continuous fun h : GA D W => (((1 : GA D V), h) : GA D V × GA D W) :=
    continuous_const.prodMk continuous_id
  have hcont1' : Continuous fun h : GA D W => (((1 : GA D V'), h) : GA D V' × GA D W) :=
    continuous_const.prodMk continuous_id
  suffices hC : Continuous fun h => (c h : ℂ) from continuous_induced_rng.2 hC
  rw [continuous_iff_continuousAt]
  intro h₀

  have hne₀ : ω' (1, h₀) g ≠ 0 := by
    intro h0
    apply hne
    have hinv : ω' (1, h₀⁻¹) * ω' (1, h₀) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, Prod.mk_one_one, map_one]
    have := congrArg (fun T : Module.End ℂ (WO V' W → ℂ) => T g) hinv
    simp only [Module.End.mul_apply, h0, map_zero, Module.End.one_apply] at this
    exact this.symm
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne₀

  set Dn : GA D W → ℂ := fun h => ω' (1, h) g x with hDn
  have hDc : Continuous Dn := (hω'.om_cont g hg x).comp hcont1'
  have hD0 : Dn h₀ ≠ 0 := hx

  set Nu : GA D W → ℂ := fun h => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f₀) x with hNu
  have hNc : ContinuousAt Nu h₀ := by
    haveI : SecondCountableTopology (GA D W) := hg4
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds h₀
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f₀ hf₀
      ({(1 : GA D V)} ×ˢ K) (isCompact_singleton.prod hK)
    refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => c₀) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun h =>
        ((hres.1 _ (hω.om_pres _ _ hf₀)).1 x).aestronglyMeasurable
    · filter_upwards [hKn] with h hh
      exact Filter.Eventually.of_forall fun y =>
        hc₀ ((1 : GA D V), h) ⟨rfl, hh⟩ _
    · exact integrable_const c₀
    · exact Filter.Eventually.of_forall fun y =>
        ((hω.om_cont f₀ hf₀ _).comp hcont1).continuousAt

  have hq : ∀ h, Nu h = (c h : ℂ) * Dn h := fun h => by
    have := congrFun (hc h f₀ hf₀) x
    simpa [hNu, hDn, hgdef] using this
  have hev : ∀ᶠ h in nhds h₀, Dn h ≠ 0 := hDc.continuousAt.eventually_ne hD0
  have hdiv : ContinuousAt (fun h => Nu h / Dn h) h₀ := hNc.div hDc.continuousAt hD0
  refine hdiv.congr ?_
  filter_upwards [hev] with h hh
  rw [hq h, mul_div_assoc, div_self hh, mul_one]

end GlobalTheory.TowerRestrictChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

variable {n : ℕ}

theorem mul_inv_mem_UH {G G₀ A B : Mx n} (hB : IsUnit B) (hA : Aᴴ * G * A = G₀) (hB' : Bᴴ * G * B = G₀) :
    A * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)
  show (A * B⁻¹)ᴴ * G * (A * B⁻¹) = G
  calc (A * B⁻¹)ᴴ * G * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * G * A) * B⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [hA, ← hB']; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h]; simp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

def uIso (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) : H ≃ₗᵢ[ℂ] H :=
  { toFun := σ a
    invFun := σ b
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := fun w => by
      show σ b (σ a w) = w
      rw [← sigma_mul hσ hb ha, hba, sigma_one hσ]
    right_inv := fun w => by
      show σ a (σ b w) = w
      rw [← sigma_mul hσ ha hb, hab, sigma_one hσ]
    norm_map' := hσ.2.1 a ha }

theorem uIso_apply (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) (w : H) : uIso hσ ha hb hab hba w = σ a w := rfl

end GlobalTheory.KFinCuspAvgType

end

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

theorem isTypeAt_avgN : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N _ τ e _ he φ hφ
  obtain ⟨H, i1, i2, σ, lam, ε', P, hE, hD, hP, hJ, hx⟩ := hφ.2.2 τ
  obtain ⟨-, hε⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  subst hε
  haveI : CompleteSpace H := hD.1
  have hσ : Std (N.M.ε τ) σ := std_of_isDS hPr.harishChandraModules hD
  have hσ1 := hσ.1
  set fr := N.M.fr τ with hfr
  have hf := N.M.fr_unit τ
  have hfJ := N.M.fr_gram τ
  rw [← hfr] at hf hfJ
  have hdP := (isUnit_iff_isUnit_det _).1 hP
  have hdf := (isUnit_iff_isUnit_det _).1 hf
  have hG : IsUnit (gramAt D N.V τ) := isUnit_gram hP hJ
  have hc1 : fr * P⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hP hfJ hJ
  have hc2 : P * fr⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hf hJ hfJ
  have e12 : fr * P⁻¹ * (P * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.mul_nonsing_inv _ hdf]
  have e21 : P * fr⁻¹ * (fr * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdP]
  have hconj : ∀ {Q : Mx N.V.rank}, IsUnit Q → Qᴴ * Jm (N.M.ε τ) * Q = gramAt D N.V τ →
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), Q * g * Q⁻¹ ∈ UJset (N.M.ε τ) := fun {Q} hQ hQJ g hg =>
    mul_inv_mem_UH hQ (by
      calc (Q * g)ᴴ * Jm (N.M.ε τ) * (Q * g) = gᴴ * (Qᴴ * Jm (N.M.ε τ) * Q) * g := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D N.V τ := by rw [hQJ]; exact hg) hQJ
  refine ⟨H, i1, i2, σ, lam, N.M.ε τ, fr, hE, hD, hf, hfJ, fun x => ?_⟩

  have h1 := hasTypeAll_iff.2 (hx x)
  have h2 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) σ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr hG hf hfJ
    (uIso hσ1 hc1 hc2 e12 e21) (fun g hg v => by
      rw [uIso_apply, uIso_apply, ← sigma_mul hσ1 hc1 (hconj hP hJ g hg), ← sigma_mul hσ1 (hconj hf hfJ g hg) hc1]
      congr 2
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.nonsing_inv_mul_cancel_left _ _ hdf]) _ h1
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := h2
  have h3 := GlobalTheory.SeriesToClosure.moves_avg hθ hf hfJ hσ he φ x S v ℓ C hS hc h
  have h4 : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x) := ⟨S, hS, hc, _, ℓ, C, h3⟩
  have hfi : IsUnit fr⁻¹ := (isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hdf)
  have hfiJ : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hdf]; simp
  have h5 := hasTypeAll_transport _ H H σ (fun g => σ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfi hfiJ (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ g w = σ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [Matrix.nonsing_inv_nonsing_inv _ hdf]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdf,
        Matrix.mul_one]) _ h4
  have e5 : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x (fr⁻¹⁻¹ * y * fr⁻¹)) =
      fun y => GlobalTheory.KFinCuspApprox.avgN θ N τ e φ (x * atTau θ N.V τ y) := funext fun y => by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdf, GlobalTheory.SeriesToClosure.res_conj hf]
  rw [e5] at h5
  exact hasTypeAll_iff.1 h5

end GlobalTheory.KFinCuspAvgType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgIsCusp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp

namespace GlobalTheory.KFinCuspApprox

theorem isCuspFun_avgN : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D)
    (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ →
    IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro D θ hθ _ N τ e he φ hφ hc
  set A : Formalism.REAL.KG (N.M.ε τ) → GA D N.V :=
    fun k => atTau θ N.V τ ((N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ) with hA
  have hAc : Continuous A := (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
    GlobalTheory.SeriesToClosure.continuous_conjK fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hl : LeftInv (GQ N.V) φ := hφ.left
  have havg : ∀ x, GlobalTheory.KFinCuspApprox.avgN θ N τ e φ x = ∫ k, e k * φ (x * A k) ∂(Formalism.REAL.muK (N.M.ε τ)) :=
    fun x => rfl
  have hlA : LeftInv (GQ N.V) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := fun γ hγ g => by
    simp only [havg, mul_assoc, hl γ hγ]
  refine (isCuspFun_iff hlA).2 fun W hW => funext fun x => ?_
  have hcc := cocompact_single hW
  have h0 := congrFun ((isCuspFun_iff hl).1 hc W hW)
  set NN := NA (IsoFlag.single hW) with hNN
  have h𝓕 := isFundamentalDomain_stdDom ((GQ N.V).subgroupOf NN) (Measure.haar : Measure NN)
  have hfin := hcc.measure_ne_top h𝓕
  show constTermOn (GQ N.V) NN _ x = 0
  rw [hcc.constTermOn_eq_zero_iff h𝓕 hlA x]
  have hz : ∀ y, ∫ n in stdDom ((GQ N.V).subgroupOf NN), φ ((n : GA D N.V) * y) ∂(Measure.haar : Measure NN) = 0 :=
    fun y => (hcc.constTermOn_eq_zero_iff h𝓕 hl y).1 (h0 y)
  obtain ⟨K0, hK0, hs⟩ := hcc
  have hcont : Continuous fun p : NN × Formalism.REAL.KG (N.M.ε τ) => φ ((p.1 : GA D N.V) * x * A p.2) :=
    hφ.cont.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hAc.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hK0.prod (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hb : ∀ (n : NN) k, ‖φ ((n : GA D N.V) * x * A k)‖ ≤ C := fun n k => by
    obtain ⟨γ, hγ, hk⟩ := hs n
    have h1 := hC (γ * n, k) ⟨hk, trivial⟩
    have h2 := hl ((γ : NN) : GA D N.V) (Subgroup.mem_subgroupOf.1 hγ) ((n : GA D N.V) * x * A k)
    simp only [Subgroup.coe_mul] at h1
    have e1 : ((γ : NN) : GA D N.V) * n * x * A k = (γ : GA D N.V) * ((n : GA D N.V) * x * A k) := by
      simp only [mul_assoc]
    rwa [e1, h2] at h1
  obtain ⟨Ce, hCe⟩ := (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ))).exists_bound_of_continuousOn he.continuousOn
  haveI : IsFiniteMeasure ((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))) :=
    isFiniteMeasure_restrict.2 hfin
  have hint : Integrable (Function.uncurry fun (n : NN) (k : Formalism.REAL.KG (N.M.ε τ)) => e k * φ ((n : GA D N.V) * x * A k))
      (((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))).prod (Formalism.REAL.muK (N.M.ε τ))) := by
    refine Integrable.mono' (integrable_const (Ce * C)) ?_ (ae_of_all _ fun p => ?_)
    · exact ((he.comp continuous_snd).mul hcont).aestronglyMeasurable
    · show ‖e p.2 * φ ((p.1 : GA D N.V) * x * A p.2)‖ ≤ Ce * C
      rw [norm_mul]
      exact mul_le_mul (hCe p.2 trivial) (hb p.1 p.2) (norm_nonneg _) ((norm_nonneg _).trans (hCe p.2 trivial))
  calc ∫ n in stdDom ((GQ N.V).subgroupOf NN), GlobalTheory.KFinCuspApprox.avgN θ N τ e φ ((n : GA D N.V) * x)
        ∂(Measure.haar : Measure NN)
      = ∫ n in stdDom ((GQ N.V).subgroupOf NN), ∫ k, e k * φ ((n : GA D N.V) * x * A k) ∂(Formalism.REAL.muK (N.M.ε τ))
        ∂(Measure.haar : Measure NN) := by simp only [havg]
    _ = ∫ k, ∫ n in stdDom ((GQ N.V).subgroupOf NN), e k * φ ((n : GA D N.V) * x * A k)
        ∂(Measure.haar : Measure NN) ∂(Formalism.REAL.muK (N.M.ε τ)) := integral_integral_swap hint
    _ = ∫ k, e k * 0 ∂(Formalism.REAL.muK (N.M.ε τ)) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [integral_const_mul, ← hz (x * A k)]
        simp only [mul_assoc]
    _ = 0 := by simp

end GlobalTheory.KFinCuspApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestFunctionTraceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_test_function_trace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (ρ : D.what₂.Tau) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (X →L[ℂ] X)), IsIrrUnitary δ → ∃ c, HasTrace (repOp δ (μa (placeOf D ρ)) (fa (placeOf D ρ))) c ∧ (c ≠ 0 → IsUnitEquiv δ (dsRep M ρ)) := by
  first | exact @GlobalTheory.ArchTrace.trace_pseudoCoeff_arch | exact GlobalTheory.ArchTrace.trace_pseudoCoeff_arch | (intros; apply GlobalTheory.ArchTrace.trace_pseudoCoeff_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNormInj

open GlobalTheory.MixModel

theorem phase_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y' : Mx D r W.rank) (u : Mx D W.rank r) :
    GlobalTheory.LeviNorm.phase ψ W (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W)))) u =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y' : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) := by
  rw [GlobalTheory.LeviNorm.phase_apply, adj_adj]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel]

theorem eq_of_phase_integral_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  intro D ψ hψ W r μ hμ N₁ N₂ hc₁ hc₂ hi₁ hi₂ h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D W.rank r
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hcont : ∀ y : Mx D r W.rank, Continuous fun u : Mx D W.rank r =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) :=
    fun y => hψ.1.1.comp (ht.comp (continuous_finset_sum _ fun i _ =>
      ((continuous_const.matrix_mul continuous_id).matrix_elem i i)))
  have hint : ∀ (y : Mx D r W.rank) (N : Mx D W.rank r → ℂ), Integrable N μ → Integrable (fun u =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) * N u) μ := by
    intro y N hN
    have := hN.mul_bdd (hcont y).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall fun u => (hψ.1.2.1 _).le)
    simpa only [mul_comm] using this
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicMatFourier.eq_zero_of_fourier_eq_zero D ψ hψ W.rank r μ hμ (N₁ - N₂) (hc₁.sub hc₂) (hi₁.sub hi₂) fun y' => ?_
  have e := h (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W))))
  simp only [phase_eq] at e
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub (hint y' N₁ hi₁) (hint y' N₂ hi₂), e, sub_self]

end GlobalTheory.LeviNormInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addEquiv_symplecticCoords_orientedModel : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (c : D.host.E), c ≠ 0 →
    ∃ f : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      ∀ u, f u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords | exact GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords | (intros; apply GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords <;> assumption)
end


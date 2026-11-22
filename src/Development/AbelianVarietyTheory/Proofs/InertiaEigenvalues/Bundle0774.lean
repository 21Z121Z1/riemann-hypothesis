import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import GroundTheory.LocalFields.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompactStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_mem_maxCompactGL_iff_mem_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w n ↔ y ∈ Umax L n) := by
  first | exact @GlobalTheory.LocInteg.cLoc_mem_KGL_iff | exact GlobalTheory.LocInteg.cLoc_mem_KGL_iff | (intros; apply GlobalTheory.LocInteg.cLoc_mem_KGL_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAll
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.HubX.lgcG_of_adm : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.HubX.LgcG D := by
  intro D ht h1 h2 h5 i r hr w _hwS hwg x
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, hl⟩ := GlobalTheory.T.exists_galois_rep_base_change D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.galois_rep_unique_base_change D h5 i r hr x P Pa hP hPa ρ hc hss (fun w _ => hwd w)
  refine ⟨P, hP, ?_⟩
  obtain ⟨k, hk⟩ := hwg
  have hsp : IsSplitPl D.host w :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
  rw [← hPa.2.2.2.1 w hsp, ← hwd w]
  have hok : SumRepresentations.At.WDok D.nd D.naut i ρ w := by
    by_cases hwl : w ∈ placesOver D.host.E (D.nd.l i)
    · exact Or.inr (hl w hwl).1
    · exact Or.inl hwl
  exact ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerUnipotentConjBlockFormulas
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_conj_block_formulas : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  first | (exact @GlobalTheory.SchurExt.schur_mul_conjLowUni) | (exact GlobalTheory.SchurExt.schur_mul_conjLowUni) | (intros; apply GlobalTheory.SchurExt.schur_mul_conjLowUni  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentityStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  first | exact @GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | exact GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | (intros; apply GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSubgroupOfTrivOutsideOfLocalPointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subgroup_of_trivOutside_of_local_points : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (K : Subgroup (GAf L n)) (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (y : GAf L n), TrivOutside (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) y → (∀ v ∈ T, ∃ p ∈ K, TrivOutside {v} p ∧ (p.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)) → y ∈ K := by
  first | exact @GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local | exact GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local | (intros; apply GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivativesStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  first | exact @GlobalTheory.JSW.norm_fderiv_chart_le | exact GlobalTheory.JSW.norm_fderiv_chart_le | (intros; apply GlobalTheory.JSW.norm_fderiv_chart_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureTensorOTransSumLin
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum

theorem pureTensorO_finsetSum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pureTensorO_transSum_lin : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ [Fintype (Fin V.rank → LevQ Dw l₂)] (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : PolF D W.rank V.rank), pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w) P = ∑ q, w q • pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ (fun q' => if q' = q then 1 else 0)) P := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hv ι l₂ e he _ BV BW w P
  have hψ : IsStdChar D ψ (-1) := hv.2.2.2.2.2.2.2.2.1
  have hθ : IsInfFam θ := hv.1.inf
  have hf₀ : IsThetaFunO ψ V W f₀ := hv.2.2.2.2.2.2.2.2.2.2
  have hinf : infPart D e = 0 := by
    obtain ⟨Q, hQ, -⟩ := he
    exact GlobalTheory.PlaceDatum.infPart_idemSum hQ
  have hpt : ∀ q, (levPoint V W l₂ ι e q).map (infPart D) = 0 := by
    intro q
    ext a b
    simp [levPoint, Matrix.map_apply, map_mul, hinf]
  have hth : ∀ q, IsThetaFunO ψ V W (heisO ψ V W (levPoint V W l₂ ι e q) f₀) := fun q =>
    ((GlobalTheory.FinTranslate.finite_translate D ψ θ V W hψ hθ f₀ hf₀).2 _ (hpt q)).1
  have key : ∀ w' : (Fin V.rank → LevQ Dw l₂) → ℂ,
      pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w') P =
        ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
          pureTensorO ψ θ V W (fun _ => 1) s BV BW (heisO ψ V W (levPoint V W l₂ ι e q) f₀) P := by
    intro w'
    have h1 : transSum ψ V W l₂ ι e f₀ w' = ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
        heisO ψ V W (levPoint V W l₂ ι e q) f₀ := by
      unfold transSum
      rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul]
    rw [h1]
    exact (pureTensorO_finsetSum hψ hθ (fun _ => 1) BV s BW Finset.univ _ _ hth P).2
  rw [key w]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [key, Finset.sum_eq_single q]
  · rw [if_pos rfl, mul_one, mul_comm, ← smul_smul]
  · intro b _ hb
    rw [if_neg hb, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ q) h

end GlobalTheory.SingleDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficientStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  first | exact @GlobalTheory.JSW.isRapidInf_mul_adCoef | exact GlobalTheory.JSW.isRapidInf_mul_adCoef | (intros; apply GlobalTheory.JSW.isRapidInf_mul_adCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatakeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_product_speh_satake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (recT T hL) ∧ RecSpeh (recT T hL) ∧ RecSatake (recT T hL) := by
  first | exact @GlobalTheory.FormDict.RecTLaws.recLaws_recT | exact GlobalTheory.FormDict.RecTLaws.recLaws_recT | (intros; apply GlobalTheory.FormDict.RecTLaws.recLaws_recT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictEqInvLocalArtinMap
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
open GroundTheory.LocalField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompare

theorem restrict_eq_inv_localArtinMap : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
        (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
  have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
  obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
  have e2 : ψ σ = g := by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
  have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
      (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
    restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
  have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
      [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
      a τ ∈ (normUnits (w.adicCompletion E) L).range →
        restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
    have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
    rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
    exact this
  let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
  have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
  have hker : a'.ker ≤ r.ker := fun τ hτ => by
    have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
    refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
    rw [map_one]
    exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
  let b := a'.liftOfSurjective ha' ⟨r, hker⟩
  have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
    MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
  have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
    refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
    · obtain ⟨τ, rfl⟩ := ha' π
      have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
      rw [ha.ord_eq, deg_inv, neg_neg] at h1
      have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb, hr]
      refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
      rw [unramifiedDegree_eq_ofAdd_one_iff]
      rintro ξ ⟨n, hn, hξ⟩
      have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := resCard_eq_normV w
      rw [hq] at hξ ⊢
      refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
      have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (one_lt_normV w)))).symm
      rw [h2, pow_succ, hξ, one_mul]
    · obtain ⟨τ, rfl⟩ := ha' x
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb]
      exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
  rw [← map_inv, ← hbφ, hb, ← e2]
  rfl

theorem restrict_eq_inv_reciprocity : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (Ω' : Type) [Field Ω'] [Algebra (w.adicCompletion E) Ω'] [IsSepClosure (w.adicCompletion E) Ω'] (j : Ω →+* Ω'),
    (∀ x : E, j (algebraMap E Ω x) = algebraMap (w.adicCompletion E) Ω' (algebraMap E (w.adicCompletion E) x)) →
    (∀ z : Ω, z ∈ A ↔ ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).IsIntegralElem (j z)) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ (σ : Weil h) (g : Ω' ≃ₐ[w.adicCompletion E] Ω'), (∀ z : Ω, g (j z) = j ((σ : G E Ω) z)) →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
        (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ ∧
      ∀ (M : IntermediateField (w.adicCompletion E) Ω') [FiniteDimensional (w.adicCompletion E) M]
        [IsAbelianGalois (w.adicCompletion E) M],
        AlgEquiv.restrictNormalHom M g =
          ((localReciprocityAbelian M).symm
            (a σ : (w.adicCompletion E)ˣ ⧸ (normUnits (w.adicCompletion E) M).range))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h Ω' _ _ _ j hj hA a ha σ g hg
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : IsSepClosure (w.adicCompletion E) (Kbar w) := ⟨inferInstance, inferInstance⟩
  let ε : Ω' ≃ₐ[w.adicCompletion E] Kbar w := IsSepClosure.equiv (w.adicCompletion E) Ω' (Kbar w)
  let ι : Ω →ₐ[E] Kbar w :=
    { (ε : Ω' →+* Kbar w).comp j with
      commutes' := fun x => by
        change ε (j (algebraMap E Ω x)) = _
        rw [hj, ε.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)] }
  have hιz : ∀ z, ι z = ε (j z) := fun _ => rfl
  have hc : (ε : Ω' →+* Kbar w).comp ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) =
      algebraMap (w.adicCompletionIntegers E) (Kbar w) := RingHom.ext fun x => by
    rw [IsScalarTower.algebraMap_apply (w.adicCompletionIntegers E) (w.adicCompletion E) (Kbar w)]
    exact ε.commutes _
  have hι : IsLocEmb A w ι := fun z => by
    rw [hA, hιz]
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      rw [← hc]
      have := congrArg (ε : Ω' →+* Kbar w) hp'
      rwa [Polynomial.hom_eval₂, map_zero] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (ε : Ω' →+* Kbar w).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hc]
      exact hp'
  let g' : GalLoc w := ε.symm.trans (g.trans ε)
  have hg' : Lifts ι g' σ := fun z => by
    change ε (g (ε.symm (ε (j z)))) = ε (j _)
    rw [ε.symm_apply_apply, hg]
  have H := restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ g' hg'
  have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
      (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ := by
    rw [← map_inv] at H ⊢
    ext y
    have h1 := localArtinMap_transport (RingEquiv.refl (w.adicCompletion E)) (fun _ _ => Iff.rfl)
      (ε : Ω' ≃+* Kbar w) (fun x => ε.commutes x) (a σ)⁻¹ y.2
    have h2 : Units.map (RingEquiv.refl (w.adicCompletion E)).toRingHom.toMonoidHom (a σ)⁻¹ = (a σ)⁻¹ :=
      Units.ext rfl
    rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
    rw [AlgEquiv.restrictNormalHom_apply]
    apply ε.injective
    refine Eq.trans ?_ h1.symm
    change _ = ε (g (ε.symm (ε y)))
    rw [ε.symm_apply_apply]
  refine ⟨H1, fun M _ _ => ?_⟩
  rw [← restrictAb_localArtinMap, ← map_inv, ← H1]
  exact (restrictAb_topologicalAbelianizationEquiv M (le_maximalAbelianExtension M) g).symm

end GlobalTheory.ArtinCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphismStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTransform_invariant_under_field_automorphism : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (ϖ : K) (q n m : ℕ), Formalism.UG.IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h : Formalism.UG.GU σ n → ℂ, Formalism.UG.IsBiInv (Formalism.UG.KU σ n) h → ∀ α : Fin m → ℂ, Formalism.UG.SatU ϖ q (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) α = Formalism.UG.SatU ϖ q h α := by
  first | exact @GlobalTheory.SatInvAuto.satU_guMap_self | exact GlobalTheory.SatInvAuto.satU_guMap_self | (intros; apply GlobalTheory.SatInvAuto.satU_guMap_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlaceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS E (m + 1) S := by
  first | (exact @GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (exact GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (intros; apply GlobalTheory.SchurExt.mkGL_Scof_mem_supS  <;> assumption)
end


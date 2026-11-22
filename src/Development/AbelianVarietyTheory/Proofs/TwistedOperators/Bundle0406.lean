import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelParabolicDeterminantAbsOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIndicatorProjFinSmul
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
namespace GlobalTheory.TrOpTensor

theorem exists_sum_indicator {X W : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup W] [Module ℂ W]
    (F : X → W) (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ s : Finset W, (∀ r ∈ s, IsOpen (F ⁻¹' {r}) ∧ IsCompact (closure (F ⁻¹' {r}))) ∧
      ∀ x, F x = ∑ r ∈ s, (F ⁻¹' {r}).indicator (fun _ => (1 : ℂ)) x • r := by
  classical
  have hfin : (Set.range F).Finite := by
    haveI : CompactSpace ↥(tsupport F) := isCompact_iff_compactSpace.1 hc
    have h1 : (Set.range (fun x : tsupport F => F x)).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport F
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr (image_eq_zero_of_notMem_tsupport hx)
  refine ⟨hfin.toFinset.filter (· ≠ 0), fun r hr => ?_, fun x => ?_⟩
  · have hr0 : r ≠ 0 := (Finset.mem_filter.1 hr).2
    refine ⟨hF.isOpen_fiber r, hc.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => subset_tsupport F ?_) (isClosed_tsupport F))⟩
    rw [Function.mem_support, show F x = r from hx]
    exact hr0
  · by_cases h0 : F x = 0
    · rw [h0]
      symm
      refine Finset.sum_eq_zero fun r hr => ?_
      have hx : x ∉ F ⁻¹' {r} := fun hx => (Finset.mem_filter.1 hr).2 ((show F x = r from hx).symm.trans h0)
      rw [Set.indicator_of_notMem hx, zero_smul]
    · rw [Finset.sum_eq_single (F x)]
      · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' {F x} from rfl), one_smul]
      · intro r _ hne
        rw [Set.indicator_of_notMem (s := F ⁻¹' {r}) (fun hx => hne (show F x = r from hx).symm), zero_smul]
      · intro hn
        exact absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, h0⟩) hn

theorem integralOp_eq_sum {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    (ν : Measure G) (σ : Representation ℂ G W) (b : G → ℂ) (A : W →ₗ[ℂ] W)
    (hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ b A) (w : W) (s : Finset W)
    (hs : ∀ r ∈ s, MeasurableSet ((fun h => b h • σ h w) ⁻¹' {r}) ∧ ν ((fun h => b h • σ h w) ⁻¹' {r}) ≠ ⊤)
    (hsum : ∀ h, b h • σ h w = ∑ r ∈ s, ((fun h => b h • σ h w) ⁻¹' {r}).indicator (fun _ => (1 : ℂ)) h • r) :
    A w = ∑ r ∈ s, ((ν ((fun h => b h • σ h w) ⁻¹' {r})).toReal : ℂ) • r := by
  set F := fun h => b h • σ h w with hF
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have hpt : ∀ h, b h * l (σ h w) = ∑ r ∈ s, (F ⁻¹' {r}).indicator (fun _ => l r) h := by
    intro h
    rw [← smul_eq_mul, ← map_smul]
    change l (b h • σ h w) = _
    rw [hsum h, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, smul_eq_mul]
    by_cases hh : h ∈ F ⁻¹' {r}
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, one_mul]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, zero_mul]
  rw [map_sub, (hA w l).2, map_sum, integral_congr_ae (.of_forall hpt),
    integral_finsetSum _ fun r hr => (integrableOn_const (hs r hr).2).integrable_indicator (hs r hr).1,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [integral_indicator_const _ (hs r hr).1, map_smul, Measure.real, Complex.real_smul, smul_eq_mul, sub_self]

theorem measure_eq_of_isFinMeas {D : D7} (V : HSp D) {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {νF : Measure (GFin D.sp.cm.sig V.gram)} (hF : IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF)
    {ν : Measure (GfC V)} (hν : IsFinMeas V μf ν) (s : Set (GfC V)) (hs : IsCompact (closure s)) :
    ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := GlobalTheory.T.haar_eq_restrictedProductMeasure_unitaryFiniteAdelic D V μf νF hF ν hν s hs

theorem integral_indicator_projFin_smul {D : D7} (V : HSp D) {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)}
    {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)}
    (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ)
    {νF : Measure (GFin D.sp.cm.sig V.gram)} (hF : IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (B : Set (GFin D.sp.cm.sig V.gram)) (hB : MeasurableSet B) (hB' : νF B ≠ ⊤)
    (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E) (ha : Integrable a (Measure.pi μa)) :
    Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧
    ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa :=
  GlobalTheory.T.integral_finiteIndicator_smul_archFunction D V μa μf μ hμ νF hF E B hB hB' a ha

open scoped Classical in

theorem integral_pi_dsRep {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, SigmaFinite (μa w)]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : ContinuousMultilinearMap ℂ M.H H) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (y : ∀ τ, M.H τ)
    (hfa : ∀ τ, Integrable (fun z => fa (placeOf D τ) z • dsRep M τ z (y τ)) (μa (placeOf D τ))) :
    Integrable (fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
        (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))) (Measure.pi μa) ∧
    ∫ x, (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ)) ∂Measure.pi μa =
      Φ fun τ => ∫ z, fa (placeOf D τ) z • dsRep M τ z (y τ) ∂μa (placeOf D τ) := by
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (isIrrUnitary_dsRep M τ).complete
  have hgen := GlobalTheory.T.integral_continuousMultilinearMap_pi_measure D.what₂.Tau (fun τ => GArch D.sp.cm.sig V.gram (placeOf D τ))
    (fun τ => μa (placeOf D τ)) M.H H Φ (fun τ z => fa (placeOf D τ) z • dsRep M τ z (y τ)) hfa
  obtain ⟨e, he⟩ : ∃ e : D.what₂.Tau ≃ InfinitePlace D.host.F, e = Equiv.ofBijective _ (placeOf_bijective D) := ⟨_, rfl⟩
  subst he
  have hP := measurePreserving_piCongrLeft μa (Equiv.ofBijective _ (placeOf_bijective D))
  set P := MeasurableEquiv.piCongrLeft (fun w => GArch D.sp.cm.sig V.gram w)
    (Equiv.ofBijective _ (placeOf_bijective D)) with hPdef
  have hcomp : ∀ x' : ∀ τ, GArch D.sp.cm.sig V.gram (placeOf D τ),
      (∏ w, fa w (P x' w)) • Φ (fun τ => dsRep M τ (P x' (placeOf D τ)) (y τ)) =
        Φ fun τ => fa (placeOf D τ) (x' τ) • dsRep M τ (x' τ) (y τ) := by
    intro x'
    have hx : ∀ τ, P x' (placeOf D τ) = x' τ := fun τ =>
      Equiv.piCongrLeft_apply_apply (fun w => GArch D.sp.cm.sig V.gram w)
        (Equiv.ofBijective _ (placeOf_bijective D)) x' τ
    rw [ContinuousMultilinearMap.map_smul_univ,
      ← Equiv.prod_comp (Equiv.ofBijective _ (placeOf_bijective D)) (fun w => fa w (P x' w))]
    refine congrArg₂ (· • ·) (Finset.prod_congr rfl fun τ _ => ?_) (congrArg Φ (funext fun τ => ?_))
    · exact congrArg (fa (placeOf D τ)) (hx τ)
    · exact congrArg (fun z => dsRep M τ z (y τ)) (hx τ)
  have hfun : ((fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
      (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))) ∘ P) =
      fun x' => Φ fun τ => fa (placeOf D τ) (x' τ) • dsRep M τ (x' τ) (y τ) := funext hcomp
  refine ⟨?_, ?_⟩
  · rw [← hP.integrable_comp_emb P.measurableEmbedding, hfun]
    exact hgen.1
  · rw [← hP.integral_comp' (fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
      (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))), ← hgen.2]
    exact integral_congr_ae (.of_forall hcomp)

open scoped Classical in

theorem apply_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {W : Type} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ (GfC V) W} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H}
    (hT : T ∈ homFinDS σ M π ⊤) (g : GA D V) (w : W) (y : ∀ τ, M.H τ) :
    π g (T w y) = T (σ (toFin V g) w) fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  have h := mem_homTensorPi.1 hT
  have e := GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise D V S M H π ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
  calc π g (T w y) = π (toInf V g : GA D V) (π (toFin V g : GA D V) (T w y)) := by
        conv_lhs => rw [← toInf_mul_toFin g]
        rw [map_mul]; rfl
    _ = π (toInf V g : GA D V) (T (σ (toFin V g) w) y) := by rw [h.2.1]; rfl
    _ = _ := e

end GlobalTheory.TrOpTensor

namespace GlobalTheory.TrOpTensor

theorem locallyConstant_smul {D : D7} (V : HSp D) {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hσ : GlobalTheory.PRep.IsSmooth σ) (w : W) :
    IsLocallyConstant (fun h => finFn V ff h • σ h w) ∧ HasCompactSupport (fun h => finFn V ff h • σ h w) := by
  obtain ⟨hlc, hcs⟩ := GlobalTheory.FinTrace.finFn_mem_SB V hff
  have h2 : IsLocallyConstant fun h : GfC V => σ h w := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun h => x⁻¹ * h) ⁻¹' {g | σ g w = w},
      (hσ w).preimage (continuous_const.mul continuous_id), by simp, fun x' hx' => ?_⟩
    have e : x' = x * (x⁻¹ * x') := by group
    rw [e, map_mul, Module.End.mul_apply, show σ (x⁻¹ * x') w = w from hx']
  exact ⟨hlc.comp₂ h2 (fun a b => a • b), hcs.smul_right⟩

theorem finFn_toFin {D : D7} (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GA D V) :
    finFn V ff (toFin V g) = ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v g) := by
  unfold finFn
  refine finprod_congr fun v => congrArg (ff v) ?_
  change proj D.sp.cm.sig V.gram v (ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g)) = _
  rw [proj_ofFin, projFinLoc_projFin]

theorem opTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ ν, IsFinMeas V μf ν → ∀ fa ff, (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ T ∈ homFinDS σ M π ⊤, ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) A → ∀ w y, repOp π μ (tensor D.sp.cm.sig V.gram fa ff) (T w y) = T (A w) fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ)) (y τ) := by
  intro D V S M μa μf μ hμ ν hν fa ff hfa hff W _ _ σ hσ H _ _ _ π hπ T hT A hA w y
  have := hμ.haar
  have := hμ.haar_arch
  have := hμ.haar_loc
  have hfc : ∀ w', Continuous (fa w') := fun w' =>
    continuous_of_mem_ccSmooth (continuous_archCoord _ _ w') (hfa w')
  have hfs : ∀ w', HasCompactSupport (fa w') := fun w' => (hfa w').1
  have hD := fun τ => (isUnitaryRep_dsRep M τ).isRepOp (μ := μa (placeOf D τ)) (hfc (placeOf D τ)) (hfs (placeOf D τ))
  obtain ⟨hcf, hcs⟩ := continuous_of_mem_ccAd (tensor_mem_ccAd hfa hff)
  have hR := hπ.isRepOp (μ := μ) hcf hcs
  obtain ⟨hlc, hcF⟩ := locallyConstant_smul V hff hσ w
  obtain ⟨s, hs, hsum⟩ := exists_sum_indicator _ hlc hcF
  obtain ⟨νF, hνF⟩ := (existsUnique_isRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf
    hμ.eventually_eq_one).exists
  have := hν.1
  set F : GfC V → W := fun h => finFn V ff h • σ h w with hF
  have hfin : ∀ r ∈ s, ν (F ⁻¹' {r}) ≠ ⊤ := fun r hr =>
    ((measure_mono subset_closure).trans_lt (hs r hr).2.measure_lt_top).ne
  have hAw := integralOp_eq_sum ν σ (finFn V ff) A hA w s
    (fun r hr => ⟨(hs r hr).1.measurableSet, hfin r hr⟩) hsum
  set a : W → (∀ w', GArch D.sp.cm.sig V.gram w') → H := fun r x =>
    (∏ w', fa w' (x w')) • T r (fun τ => dsRep M τ (x (placeOf D τ)) (y τ)) with ha
  have hsf : ∀ w', SigmaFinite (μa w') := fun w' => inferInstance
  have hpi := fun r => integral_pi_dsRep M μa (T r) fa y fun τ => (hD τ (y τ)).1
  set B : W → Set (GFin D.sp.cm.sig V.gram) := fun r => (finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' (F ⁻¹' {r}) with hB
  have hBm : ∀ r ∈ s, MeasurableSet (B r) := fun r hr =>
    ((hs r hr).1.preimage (finPtsEquiv D.sp.cm.sig V.gram).continuous).measurableSet
  have hνB : ∀ r ∈ s, νF (B r) = ν (F ⁻¹' {r}) := fun r hr =>
    (measure_eq_of_isFinMeas V hνF hν _ (hs r hr).2).symm
  have hBf : ∀ r ∈ s, νF (B r) ≠ ⊤ := fun r hr => by rw [hνB r hr]; exact hfin r hr
  have hL := fun r (hr : r ∈ s) => integral_indicator_projFin_smul V hμ hνF (B r) (hBm r hr) (hBf r hr) (a r) (hpi r).1
  have hpt : ∀ g : GA D V, tensor D.sp.cm.sig V.gram fa ff g • π g (T w y) =
      ∑ r ∈ s, (B r).indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a r (fun w' => projArch D.sp.cm.sig V.gram w' g) := by
    intro g
    rw [apply_homFinDS hT, tensor, ← finFn_toFin, mul_smul, ← ContinuousMultilinearMap.smul_apply,
      ← LinearMap.map_smul, hsum, map_sum, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_comm]
    rfl
  rw [(hR (T w y)).2, integral_congr_ae (.of_forall hpt), integral_finset_sum _ fun r hr => (hL r hr).1,
    hAw, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [(hL r hr).2, (hpi r).2, map_smul, ContinuousMultilinearMap.smul_apply, hνB r hr, Complex.coe_smul]
  congr 2
  funext τ
  exact ((hD τ (y τ)).2).symm

end GlobalTheory.TrOpTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameInvMul
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
open scoped TensorProduct

namespace GlobalTheory.SplitPlaceRed

theorem isFrame_inv_mul {D : D7} {n : ℕ} {L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (β A : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (hA : A.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) L : Set (Fin n → Formalism.IndefR.Lev.EAf D)) =
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin n → Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.IsFrame (A⁻¹ * β) L := by
  intro x
  have hAm : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) L ↔ A.1.mulVec z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    intro z
    constructor
    · intro hz
      rw [← SetLike.mem_coe, ← hA]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [← SetLike.mem_coe, ← hA] at hz
      obtain ⟨z', hz', e⟩ := hz
      have e2 := congrArg (A⁻¹).1.mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at e2
      exact e2 ▸ hz'
  rw [hAm, hβ]
  have e : ((A⁻¹ * β)⁻¹).1 = (β⁻¹).1 * A.1 := by
    rw [mul_inv_rev, inv_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 1000000 in

theorem map_intGL_eq {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (A : GA D V) (g : Gv V v)
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = finE V (A * embV V v g * A⁻¹)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β))⁻¹ * splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g *
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β) := by
  set Φ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) →* GL (Fin V.rank) (Fv D.host.F v) :=
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) with hΦ
  have hfin : ∀ h : GA D V, Φ (finE V h) = Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom V h) := by
    intro h
    apply Units.ext
    apply Matrix.ext
    intro p q
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((finE V h).1 p q) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ ((Formalism.L2.Theta.matHom V h).1 p q)
    rw [GlobalTheory.LevSplit.finE_val]
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hk : Φ (finE V (embV V v g)) = splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g := by
    rw [hfin]
    exact GlobalTheory.SplitChartLink.rdA_matHom_embV V φ _
  have hyv : Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
    show _ = β⁻¹ * (β * _ * β⁻¹) * β
    group
  rw [hyv, hy]
  show _ = (Φ ((finE V A)⁻¹ * β))⁻¹ * _ * Φ ((finE V A)⁻¹ * β)
  simp only [map_mul, map_inv, hk]
  group

end GlobalTheory.SplitPlaceRed

namespace GlobalTheory.SplitPlaceRed

set_option maxHeartbeats 1000000 in

theorem splitRed_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (a : GfC V), IsBaseFrame V β Λ N → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), PP.under (𝓞 D.host.F) = v → ¬ Formalism.IndefR.Lev.IsConjPl PP PP → (∀ k : Kv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β) → ∃ (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ResF v ≃+* kP PP), ∀ (k : Kv V v) (i j : Fin V.rank), (redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))).1 i j = ρ ((s.red k).1 i j) := by
  intro D V β Λ N a hB hL v PP hv hc hst

  have hcc : Formalism.IndefR.Lev.IsConjPl PP (Formalism.L2.DIV.conjPl PP) := by
    intro c hc'
    refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]
    exact hc'
  have hne : PP ≠ Formalism.L2.DIV.conjPl PP := fun e => hc (by
    have := hcc
    rw [← e] at this
    exact this)
  have hv' : (Formalism.L2.DIV.conjPl PP).under (𝓞 D.host.F) = v :=
    (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hcc).symm.trans hv
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) hne hv hv'
  set φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v := splitProj τ with hφ
  have hemb : GlobalTheory.SplitProjChart.emb φ = τ := by
    ext x; simp [hφ, GlobalTheory.SplitProjChart.emb, splitProj]

  have hfr := isFrame_inv_mul β (finE V (a : GA D V)) hB.1 hL.2
  have hsb := GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ
  let s : SplitAt D.sp.cm.sig V.gram (frameLat V) v :=
    ⟨GlobalTheory.SplitProjChart.emb φ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V (a : GA D V))⁻¹ * β), isCMExt_host D,
      GlobalTheory.ChartStab.hermND D V, GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v, hsb⟩
  have hP : splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := hemb ▸ hτ
  let ρ : ResF v ≃+* kP PP :=
    (splitResidueEquiv (GlobalTheory.SplitProjChart.emb φ)).symm.trans (Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP))
  refine ⟨s, ρ, fun k i j => ?_⟩
  obtain ⟨y, hy⟩ := hst k
  have hg0 : ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) = (a : GA D V) * embV V v (k : Gv V v) * (a : GA D V)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_locFin, Subgroup.coe_inv]
  rw [← hy, redFn_frGL]
  rw [hg0] at hy
  show resS D.host.F PP (y.1 i j) = ρ ((s.red k).1 i j)

  have hg : ∀ x : 𝓞 D.host.E, ((ρ : ResF v →+* kP PP).comp ((IsLocalRing.residue _).comp (GlobalTheory.PlaceRed.rdS φ)))
      (oToS D.host.F D.host.E x) = Ideal.Quotient.mk PP.asIdeal x := by
    intro x
    simp only [RingHom.comp_apply, GlobalTheory.PlaceRed.rdS_oToS]
    have e1 : GlobalTheory.PlaceRed.rdO φ x = splitInt (GlobalTheory.SplitProjChart.emb φ) x := Subtype.ext rfl
    rw [e1, ← splitResidueEquiv_mk]
    show Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP) ((splitResidueEquiv _).symm (splitResidueEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  rw [← GlobalTheory.PlaceRed.eq_resS PP _ hg]
  show ρ (IsLocalRing.residue _ (GlobalTheory.PlaceRed.rdS φ (y.1 i j))) = ρ ((s.red k).1 i j)
  congr 1
  have hred : (s.red k).1 i j = IsLocalRing.residue _ ((stabLocEquiv (isCMExt_host D) (GlobalTheory.ChartStab.hermND D V)
      (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v) hsb k).1 i j) := by
    show (splitRed _ _ _ _ k).1 i j = _
    rw [splitRed_val]; rfl
  rw [hred]
  congr 1
  apply Subtype.ext
  rw [coe_stabLocEquiv, splitEquivIn_apply]
  exact congrArg (fun m : GL (Fin V.rank) (Fv D.host.F v) => m.1 i j) (map_intGL_eq V φ β (a : GA D V) (k : Gv V v) y hy)

end GlobalTheory.SplitPlaceRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (g : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, ∀ u ∈ Λ, ψ (symplO S T u (t z)) = 1) → IsLatVac (heisO ψ S T) Λ (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  first | exact @GlobalTheory.LatVacComb.isLatVac_sum_heisO | exact GlobalTheory.LatVacComb.isLatVac_sum_heisO | (intros; apply GlobalTheory.LatVacComb.isLatVac_sum_heisO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.CombTheta.comb_theta | exact GlobalTheory.CombTheta.comb_theta | (intros; apply GlobalTheory.CombTheta.comb_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | exact GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | (intros; apply GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelParabolicDeterminantAbsOneStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_parabolic_determinant_abs_one : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ (u : SV (wittIndex V)) (k : GA D V), k ∈ levelAll D.sp.cm.sig V.gram L a → k ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) → absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u k) = 1 := by
  first | exact @GlobalTheory.LeviShift.CptTriv.absA_detU_eq_one | exact GlobalTheory.LeviShift.CptTriv.absA_detU_eq_one | (intros; apply GlobalTheory.LeviShift.CptTriv.absA_detU_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlaceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_decomposition_split_place : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  first | exact @GlobalTheory.IwSplitFrame.iwasawa_span_split | exact GlobalTheory.IwSplitFrame.iwasawa_span_split | (intros; apply GlobalTheory.IwSplitFrame.iwasawa_span_split <;> assumption)
end


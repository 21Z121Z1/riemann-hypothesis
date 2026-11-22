import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0325
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_closed_system_coherent : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | exact GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | (intros; apply GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_pieces_generated_by_ideal_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), Ideal.span (Set.range g) = I → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | exact GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDownStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_element_maps_closed_system_down : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ a ∈ I, MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | exact GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | (intros; apply GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquivStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((jac e' (parInd e ρ)).Equiv (jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex | exact GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex | (intros; apply GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqSmulIntegralAvg
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def AbsVanish : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (N M : Subgroup Q) [N.Normal] (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure]
  (T : Subgroup G) (_ : ∀ t ∈ T, ∃ h : t ∈ Q, (⟨t, h⟩ : Q) ∈ M)
  (μT : Measure T) [SFinite μT] [μT.IsInvInvariant]
  (F : G → ℂ), Measurable F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) →
    (∀ x, ∫ u : N, F (((u : Q) : G) * x) ∂νN = 0) → quotIntegral μ T μT F = 0

theorem integral_mul_weight_eq_zero {Q : Type} [Group Q] [MeasurableSpace Q]
    (N M : Subgroup Q) (νN : Measure N) [SFinite νN] (νM : Measure M) [SFinite νM]
    (δ : M → ℝ≥0∞) (hδ : Measurable δ) (hδt : ∀ m, δ m ≠ ∞)
    (hφ : MeasurableEmbedding (fun p : N × M => (p.1 : Q) * (p.2 : Q)))
    (f w : Q → ℂ) (w' : M → ℂ) (hw : ∀ (u : N) (m : M), w ((u : Q) * (m : Q)) = w' m)
    (hf0 : ∀ m : M, ∫ u : N, f ((u : Q) * (m : Q)) ∂νN = 0) :
    ∫ q, f q * w q ∂(((νN.prod νM).withDensity fun p => δ p.2).map
      (fun p : N × M => (p.1 : Q) * (p.2 : Q))) = 0 := by
  rw [hφ.integral_map,
    integral_withDensity_eq_integral_toReal_smul (f := fun p : N × M => δ p.2) (hδ.comp measurable_snd)
      (Filter.Eventually.of_forall fun p => lt_top_iff_ne_top.2 (hδt p.2))]
  by_cases hI : Integrable (fun p : N × M => (δ p.2).toReal • (f ((p.1 : Q) * (p.2 : Q)) *
      w ((p.1 : Q) * (p.2 : Q)))) (νN.prod νM)
  · rw [integral_prod_symm _ hI]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun m => ?_)
    simp only [hw, Pi.zero_apply]
    rw [integral_smul, integral_mul_const, hf0 m]
    simp
  · exact integral_undef hI

theorem integral_eq_smul_integral_avg {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) (Q K : Subgroup G) (νQ : Measure Q) [SFinite νQ] (κ : Measure K) [SFinite κ]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hμ : μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)))
    (F : G → ℂ) (hF : Measurable F) (hFK : ∀ k ∈ K, ∀ x, F (x * k) = F x)
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hfin : ∀ᵐ g ∂μ, ρ g < ∞)
    (hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ =
      c.toReal • ∫ q : Q, F q * (((∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ).toReal : ℝ) : ℂ) ∂νQ := by
  have hm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hg : Measurable (fun g => F g * ((ρ g).toReal : ℂ)) :=
    hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  subst hμ
  have hint' := (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).1
    ((integrable_smul_measure hc0 hct).1 hint)
  have hfin' : ∀ᵐ p ∂(νQ.prod κ), ρ ((p.1 : G) * (p.2 : G)) < ∞ :=
    ae_of_ae_map hm.aemeasurable ((Measure.absolutelyContinuous_smul hc0).ae_le hfin)
  have hint'' : Integrable (fun p : Q × K => F ((p.1 : G) * (p.2 : G)) *
      ((ρ ((p.1 : G) * (p.2 : G))).toReal : ℂ)) (νQ.prod κ) := hint'
  rw [integral_smul_measure, integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_prod _ hint'']
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hfin'] with q hq
  have hmk : Measurable fun k : K => ρ ((q : G) * (k : G)) :=
    hρ.comp (measurable_subtype_coe.const_mul _)
  have e1 : ∀ k : K, F ((q : G) * (k : G)) = F q := fun k => hFK k k.2 _
  simp only [e1]
  rw [integral_const_mul, integral_complex_ofReal, integral_toReal hmk.aemeasurable hq]

section Normalisers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def onQ (Q T : Subgroup G) (h : T ≤ Q) (t : T) : T.subgroupOf Q :=
  ⟨⟨t, h t.2⟩, Subgroup.mem_subgroupOf.2 t.2⟩

theorem measurable_onQ (Q T : Subgroup G) (h : T ≤ Q) : Measurable (onQ Q T h) :=
  (measurable_subtype_coe.subtype_mk).subtype_mk

theorem isInvInvariant_map_onQ (Q T : Subgroup G) (h : T ≤ Q) (μT : Measure T) [μT.IsInvInvariant] :
    (μT.map (onQ Q T h)).IsInvInvariant := by
  have hi : MeasurableInv T := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hi' : MeasurableInv (T.subgroupOf Q) := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  show Measure.map Inv.inv (μT.map (onQ Q T h)) = μT.map (onQ Q T h)
  rw [Measure.map_map measurable_inv (measurable_onQ Q T h)]
  have e : (Inv.inv ∘ onQ Q T h) = onQ Q T h ∘ Inv.inv := rfl
  rw [e, ← Measure.map_map (measurable_onQ Q T h) measurable_inv]
  exact congrArg (Measure.map (onQ Q T h)) (Measure.inv_eq_self μT)

theorem normaliser_onQ {Q T : Subgroup G} (hTQ : T ≤ Q) {μT : Measure T} {σ : Q → ℝ≥0∞}
    (hσ : Measurable σ) (h : ∀ q : Q, ∫⁻ t : T, σ (⟨t, hTQ t.2⟩ * q) ∂μT = 1) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) σ := by
  refine ⟨hσ, fun q => ?_⟩
  have hm : Measurable fun x : T.subgroupOf Q => σ ((x : Q) * q) :=
    hσ.comp (measurable_subtype_coe.mul_const q)
  rw [lintegral_map hm (measurable_onQ Q T hTQ)]
  exact h q

theorem normaliser_avg {Q K T : Subgroup G} (hTQ : T ≤ Q) (κ : Measure K) [SFinite κ]
    (hκ : κ Set.univ = 1) {μT : Measure T} [SFinite μT] {ρ : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ))
      (fun q => ∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ) := by
  have hm : Measurable fun p : Q × K => ρ ((p.1 : G) * (p.2 : G)) :=
    hρ.1.comp ((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd))
  refine normaliser_onQ hTQ hm.lintegral_prod_right' fun q => ?_
  rw [lintegral_lintegral_swap]
  · have key : ∀ k : K, ∫⁻ t : T, ρ (((⟨t, hTQ t.2⟩ * q : Q) : G) * (k : G)) ∂μT = 1 := fun k => by
      have := hρ.2 ((q : G) * (k : G))
      simpa [mul_assoc] using this
    simp only [key, lintegral_one, hκ]
  · have : Measurable fun p : T × K => ρ (((p.1 : G) * (q : G)) * (p.2 : G)) :=
      hρ.1.comp (((measurable_subtype_coe.comp measurable_fst).mul_const _).mul
        (measurable_subtype_coe.comp measurable_snd))
    exact this.aemeasurable

theorem normaliser_proj {Q T : Subgroup G} (hTQ : T ≤ Q) (N M : Subgroup Q) [hN : N.Normal]
    (hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M) (hdec : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m)
    (pr : Q → M) (hprm : Measurable pr) (hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m)
    {μT : Measure T} {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) (fun q => ρ ((pr q : Q) : G)) := by
  refine normaliser_onQ hTQ
    (hρ.1.comp (measurable_subtype_coe.comp (measurable_subtype_coe.comp hprm))) fun q => ?_
  obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
  have key : ∀ t : T, ((pr ((⟨t, hTQ t.2⟩ : Q) * (u * m)) : Q) : G) = (t : G) * ((m : Q) : G) := by
    intro t
    have e : (⟨t, hTQ t.2⟩ : Q) * (u * m) =
        ((⟨(⟨t, hTQ t.2⟩ : Q) * u * (⟨t, hTQ t.2⟩ : Q)⁻¹, hN.conj_mem u hu _⟩ : N) : Q) *
          ((⟨(⟨t, hTQ t.2⟩ : Q) * m, M.mul_mem (hTM t) hm⟩ : M) : Q) := by
      simp only
      group
    rw [e, hpr]
    rfl
  simp only [key]
  exact hρ.2 _

end Normalisers

theorem absVanish_of (hQK : HaarQK) (hNM : HaarNM) : AbsVanish := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec N M _ hN hM hnm hinf νN _ T hT μT _ _ F hF hFT hFK hF0
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T μT ρ
  swap
  · simp [quotIntegral, hex]
  rw [quotIntegral, dif_pos hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ
  have hTQ : T ≤ Q := fun t ht => by
    obtain ⟨h, _⟩ := hT t ht
    exact h
  have hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M := fun t => by
    obtain ⟨h, h'⟩ := hT t t.2
    exact h'
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Q := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  obtain ⟨νQ, _⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨νM, _⟩ : ∃ ν : Measure M, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨κ, _, hκ⟩ : ∃ κ : Measure K, κ.IsHaarMeasure ∧ κ Set.univ = 1 :=
    ⟨Measure.haarMeasure ⊤, inferInstance, Measure.haarMeasure_self⟩
  obtain ⟨c, hc0, hct, hμ⟩ := hQK μ Q K hQ hK hdec νQ κ
  obtain ⟨δ, hδ, hδt, hνQ⟩ := hNM νQ N M hN hM hnm hinf νN νM
  have φc : Continuous fun p : N × M => (p.1 : Q) * (p.2 : Q) := by fun_prop
  have φemb : MeasurableEmbedding fun p : N × M => (p.1 : Q) * (p.2 : Q) :=
    φc.measurableEmbedding (mulMap_injective N M hinf)
  let pr : Q → M := Function.extend (fun p : N × M => (p.1 : Q) * (p.2 : Q)) Prod.snd (fun _ => 1)
  have hprm : Measurable pr := φemb.measurable_extend measurable_snd measurable_const
  have hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m := fun u m =>
    (mulMap_injective N M hinf).extend_apply Prod.snd _ (u, m)
  have hfin := GlobalTheory.CompanionTheory.QuotNorm.ae_lt_top_of_normaliser (μG := μ) hρ
  by_cases hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ
  swap
  · exact integral_undef hint
  rw [integral_eq_smul_integral_avg μ Q K νQ κ c hc0 hct hμ F hF hFK ρ hρ.1 hfin hint]
  haveI := isInvInvariant_map_onQ Q T hTQ μT
  have hρ₁ := normaliser_avg (Q := Q) hTQ κ hκ hρ
  have hρ₂ := normaliser_proj hTQ N M hTM hnm pr hprm hpr hρ
  have e := GlobalTheory.CompanionTheory.QuotNorm.integral_normaliser_eq_of (μG := νQ) (F := fun q : Q => F q)
    (hF.comp measurable_subtype_coe)
    (fun h hh g => hFT h (Subgroup.mem_subgroupOf.1 hh) g) hρ₁ hρ₂
  have z : ∫ q : Q, F q * ((ρ ((pr q : Q) : G)).toReal : ℂ) ∂νQ = 0 := by
    rw [hνQ]
    exact integral_mul_weight_eq_zero N M νN νM δ hδ hδt φemb _ _
      (fun m => ((ρ ((m : Q) : G)).toReal : ℂ)) (fun u m => by simp only [hpr])
      (fun m => hF0 _)
  rw [e, z, smul_zero]

theorem absVanish : AbsVanish := absVanish_of haarQK haarNM

end GlobalTheory.CompanionTheory.QuotVan

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariant
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.NormaliserAbs

theorem exists_normaliser {H X : Type} [MeasurableSpace H] [MeasurableSpace X] (ν : Measure H)
    [SFinite ν]
    (act : H → X → X) (hact : Measurable (fun p : H × X => act p.1 p.2))
    (r : H → H → H) (hr : ∀ h₀, MeasurePreserving (r h₀) ν ν)
    (hrr : ∀ h₀ h x, act (r h₀ h) x = act h (act h₀ x))
    (D Z : ℕ → Set X) (hD : ∀ i, MeasurableSet (D i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hinv : ∀ i h x, act h x ∈ Z i ↔ x ∈ Z i) (hcov : ∀ x, ∃ i, x ∈ Z i)
    (hfin : ∀ i x, ν {h | act h x ∈ D i} ≠ ⊤)
    (hpos : ∀ i x, x ∈ Z i → ν {h | act h x ∈ D i} ≠ 0)
    (S : Set (X → X)) (hSD : ∀ s ∈ S, ∀ i x, s x ∈ D i ↔ x ∈ D i)
    (hSZ : ∀ s ∈ S, ∀ i x, s x ∈ Z i ↔ x ∈ Z i)
    (hSa : ∀ s ∈ S, ∀ h, ∃ s' ∈ S, ∀ x, act h (s x) = s' (act h x)) :
    ∃ ρ : X → ℝ≥0∞, Measurable ρ ∧ (∀ x, ∫⁻ h, ρ (act h x) ∂ν = 1) ∧
      ∀ s ∈ S, ∀ x, ρ (s x) = ρ x := by
  classical
  set E : ℕ → Set X := fun i => D i \ ⋃ j : {j // j < i}, Z j with hE
  have hEm : ∀ i, MeasurableSet (E i) := fun i =>
    (hD i).diff (MeasurableSet.iUnion fun j => hZ j)
  set b : X → ℝ≥0∞ := fun x => ∑' i, (E i).indicator (1 : X → ℝ≥0∞) x with hb
  have hbm : Measurable b :=
    Measurable.ennreal_tsum fun i => measurable_one.indicator (hEm i)
  set B : X → ℝ≥0∞ := fun x => ∫⁻ h, b (act h x) ∂ν with hB
  have hBm : Measurable B :=
    Measurable.lintegral_prod_left' (μ := ν) (f := fun p : H × X => b (act p.1 p.2)) (hbm.comp hact)
  have hsec : ∀ x, Measurable fun h => act h x := fun x =>
    hact.comp (measurable_id.prodMk measurable_const)
  have hind : ∀ (i : ℕ) (x : X),
      ∫⁻ h, (D i).indicator (1 : X → ℝ≥0∞) (act h x) ∂ν = ν {h | act h x ∈ D i} := by
    intro i x
    have hm : MeasurableSet {h | act h x ∈ D i} := hsec x (hD i)
    have : (fun h => (D i).indicator (1 : X → ℝ≥0∞) (act h x))
        = {h | act h x ∈ D i}.indicator 1 := by
      funext h
      by_cases hh : act h x ∈ D i
      · simp [Set.indicator, hh]
      · simp [Set.indicator, hh]
    rw [this, lintegral_indicator_one hm]

  have hBpos : ∀ x, B x ≠ 0 ∧ B x ≠ ⊤ := by
    intro x
    have hex := hcov x
    set i₀ := Nat.find hex with hi₀
    have hxi : x ∈ Z i₀ := Nat.find_spec hex
    have hmin : ∀ j < i₀, x ∉ Z j := fun j hj => Nat.find_min hex hj
    have hup : ∀ h, b (act h x) ≤
        ∑ i ∈ Finset.range (i₀ + 1), (D i).indicator (1 : X → ℝ≥0∞) (act h x) := by
      intro h
      have hz : ∀ i ∉ Finset.range (i₀ + 1), (E i).indicator (1 : X → ℝ≥0∞) (act h x) = 0 := by
        intro i hi
        have hlt : i₀ < i := by simpa [Nat.lt_succ_iff] using hi
        apply Set.indicator_of_notMem
        intro hmem
        apply hmem.2
        exact Set.mem_iUnion.2 ⟨⟨i₀, hlt⟩, (hinv i₀ h x).2 hxi⟩
      rw [hb]
      simp only
      rw [tsum_eq_sum hz]
      refine Finset.sum_le_sum fun i _ => ?_
      exact Set.indicator_le_indicator_of_subset Set.diff_subset (fun _ => zero_le) _
    have hlow : ∀ h, (D i₀).indicator (1 : X → ℝ≥0∞) (act h x) ≤ b (act h x) := by
      intro h
      have : (D i₀).indicator (1 : X → ℝ≥0∞) (act h x)
          = (E i₀).indicator (1 : X → ℝ≥0∞) (act h x) := by
        by_cases hh : act h x ∈ D i₀
        · have hmem : act h x ∈ E i₀ := by
            refine ⟨hh, fun hu => ?_⟩
            obtain ⟨⟨j, hj⟩, hjz⟩ := Set.mem_iUnion.1 hu
            exact hmin j hj ((hinv j h x).1 hjz)
          simp [Set.indicator, hh, hmem]
        · have hmem : act h x ∉ E i₀ := fun hm => hh hm.1
          simp [Set.indicator, hh, hmem]
      rw [this]
      exact ENNReal.le_tsum i₀
    constructor
    · intro h0
      have : ν {h | act h x ∈ D i₀} ≤ B x := by
        rw [← hind]
        exact lintegral_mono hlow
      exact hpos i₀ x hxi (le_antisymm (h0 ▸ this) zero_le)
    · have h1 : B x ≤ ∑ i ∈ Finset.range (i₀ + 1), ν {h | act h x ∈ D i} := by
        calc B x ≤ ∫⁻ h, ∑ i ∈ Finset.range (i₀ + 1),
              (D i).indicator (1 : X → ℝ≥0∞) (act h x) ∂ν := lintegral_mono hup
          _ = ∑ i ∈ Finset.range (i₀ + 1),
              ∫⁻ h, (D i).indicator (1 : X → ℝ≥0∞) (act h x) ∂ν := by
              refine lintegral_finset_sum _ fun i _ => ?_
              exact (measurable_one.indicator (hD i)).comp (hsec x)
          _ = _ := Finset.sum_congr rfl fun i _ => hind i x
      exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => hfin i x) h1
  have hBact : ∀ h₀ x, B (act h₀ x) = B x := by
    intro h₀ x
    have hg : Measurable fun h => b (act h x) := hbm.comp (hsec x)
    calc B (act h₀ x) = ∫⁻ h, b (act (r h₀ h) x) ∂ν :=
          lintegral_congr fun h => by rw [hrr]
      _ = B x := (hr h₀).lintegral_comp hg
  have hbS : ∀ s ∈ S, ∀ x, b (s x) = b x := by
    intro s hs x
    refine tsum_congr fun i => ?_
    have hiff : s x ∈ E i ↔ x ∈ E i := by
      simp only [hE, Set.mem_diff, Set.mem_iUnion, hSD s hs, hSZ s hs]
    by_cases hx : x ∈ E i
    · simp [Set.indicator, hx, hiff.2 hx]
    · have : s x ∉ E i := fun h => hx (hiff.1 h)
      simp [Set.indicator, hx, this]
  have hBS : ∀ s ∈ S, ∀ x, B (s x) = B x := by
    intro s hs x
    refine lintegral_congr fun h => ?_
    obtain ⟨s', hs', he⟩ := hSa s hs h
    rw [he, hbS s' hs']
  refine ⟨fun x => b x / B x, hbm.div hBm, ?_, ?_⟩
  · intro x
    have : (fun h => b (act h x) / B (act h x)) = fun h => b (act h x) * (B x)⁻¹ := by
      funext h
      rw [hBact, div_eq_mul_inv]
    simp only [this]
    have hgm : Measurable fun h => b (act h x) := hbm.comp (hsec x)
    rw [lintegral_mul_const _ hgm]
    exact ENNReal.mul_inv_cancel (hBpos x).1 (hBpos x).2
  · intro s hs x
    simp only [hbS s hs, hBS s hs]

end GlobalTheory.CompanionTheory.LocVan.NormaliserAbs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnfoldWeightedAverage
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem integral_eq_zero_of_unfolding {G H : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] [MeasurableSpace H] (ν : Measure H)
    [SFinite ν] (u : H → G) (hu : Measurable u) (w ρ : G → ℝ≥0∞) (F : G → ℂ)
    (hw : Measurable w) (hρ : Measurable ρ) (hF : Measurable F)
    (hw1 : ∀ g, ∫⁻ h, w ((u h)⁻¹ * g) ∂ν = 1) (hρu : ∀ h g, ρ (u h * g) = ρ g)
    (hF0 : ∀ q, ∫ h, F (u h * q) ∂ν = 0) : ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = 0 := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : G → ℂ, K = fun g => F g * ((ρ g).toReal : ℂ) := ⟨_, rfl⟩
  have hKm : Measurable K := by
    rw [hK]; exact hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  rw [show (∫ g, F g * ((ρ g).toReal : ℂ) ∂μ) = ∫ g, K g ∂μ by rw [hK]]
  by_cases hKi : Integrable K μ
  swap
  · exact integral_undef hKi
  obtain ⟨wT, hwT⟩ : ∃ wT : G → ℝ, wT = fun g => (w g).toReal := ⟨_, rfl⟩
  have hwTm : Measurable wT := by rw [hwT]; exact hw.ennreal_toReal
  have hs : Measurable (fun p : H × G => (u p.1)⁻¹ * p.2) :=
    (hu.comp measurable_fst).inv.mul measurable_snd
  have hone : ∀ g, ∫ h, wT ((u h)⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h => w ((u h)⁻¹ * g) := hw.comp (hu.inv.mul_const g)
    have hfin : ∀ᵐ h ∂ν, w ((u h)⁻¹ * g) < ⊤ := ae_lt_top hm (by rw [hw1]; simp)
    rw [hwT]
    simp only []
    rw [integral_toReal hm.aemeasurable hfin, hw1]; simp
  obtain ⟨φ, hφ⟩ : ∃ φ : H × G → ℂ, φ = fun p => K p.2 * (wT ((u p.1)⁻¹ * p.2) : ℂ) := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact (hKm.comp measurable_snd).mul
      (Complex.measurable_ofReal.comp (hwTm.comp hs))
  have hφi : Integrable φ (ν.prod μ) := by
    refine ⟨hφm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hφm.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono (g := fun g => ‖K g‖ₑ) ?_) hKi.2
    intro g
    have hb : ∀ h, ‖φ (h, g)‖ₑ ≤ ‖K g‖ₑ * w ((u h)⁻¹ * g) := by
      intro h
      rw [hφ, hwT]
      simp only [enorm_mul]
      gcongr
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    calc ∫⁻ h, ‖φ (h, g)‖ₑ ∂ν ≤ ∫⁻ h, ‖K g‖ₑ * w ((u h)⁻¹ * g) ∂ν := lintegral_mono hb
      _ = ‖K g‖ₑ := by
        have hm : Measurable fun h => w ((u h)⁻¹ * g) := hw.comp (hu.inv.mul_const g)
        rw [lintegral_const_mul _ hm, hw1, mul_one]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H × G → ℂ, ψ = fun p => K (u p.1 * p.2) * (wT p.2 : ℂ) := ⟨_, rfl⟩
  have hshear : MeasurePreserving (fun p : H × G => (p.1, u p.1 * p.2)) (ν.prod μ) (ν.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun h x => u h * x) (MeasurePreserving.id ν)
      ((hu.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun h => map_mul_left_eq_self μ (u h)
  have hψφ : ψ = φ ∘ (fun p : H × G => (p.1, u p.1 * p.2)) := by
    funext p
    simp [hψ, hφ]
  have hψi : Integrable ψ (ν.prod μ) := by
    rw [hψφ]
    exact hshear.integrable_comp hφm.aestronglyMeasurable |>.mpr hφi
  have step1 : ∫ g, K g ∂μ = ∫ g, ∫ h, φ (h, g) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have : ∫ h, φ (h, g) ∂ν = K g * ((∫ h, wT ((u h)⁻¹ * g) ∂ν : ℝ) : ℂ) := by
      rw [hφ, ← integral_complex_ofReal, ← integral_const_mul]
    simp only [this, hone g, Complex.ofReal_one, mul_one]
  have step2 : ∫ g, ∫ h, φ (h, g) ∂ν ∂μ = ∫ h, ∫ g, φ (h, g) ∂μ ∂ν :=
    (integral_integral_swap (f := fun h g => φ (h, g)) hφi).symm
  have step3 : ∫ h, ∫ g, φ (h, g) ∂μ ∂ν = ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    have := integral_mul_left_eq_self (μ := μ) (fun g => φ (h, g)) (u h)
    simp only []
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [hψ, hφ]
  have step4 : ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν = ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ :=
    integral_integral_swap (f := fun h g => ψ (h, g)) hψi
  have step5 : ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ = 0 := by
    have : ∀ g, ∫ h, ψ (h, g) ∂ν = 0 := by
      intro g
      have e : ∀ h, ψ (h, g) = (((ρ g).toReal : ℂ) * (wT g : ℂ)) * F (u h * g) := by
        intro h
        rw [hψ, hK]
        simp only [hρu]
        ring
      simp only [e]
      rw [integral_const_mul, hF0, mul_zero]
    simp [this]
  rw [step1, step2, step3, step4, step5]

end GlobalTheory.CompanionTheory.LocVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventuallyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_operators_span_eventually : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded | exact GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded <;> assumption)
end


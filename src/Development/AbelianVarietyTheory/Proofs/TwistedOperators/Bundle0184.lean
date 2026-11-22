import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSkewElementUnitAtFinitePlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CMSkewUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cm_exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)
  by_contra hne
  push_neg at hne
  apply hc
  ext x
  have hx := h.2.2.2 w.embedding x
  rw [hne x] at hx
  simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm

theorem cm_exists_skew (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨x, hx⟩ := cm_exists_moved σ h
  refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  rw [map_sub, cm_sigma_sigma σ h]; ring

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_unit_of_val_eq_one {F : Type} [Field F] [NumberField F] {v : Pl F} {x : Fv F v} (hx : Valued.v x = 1) :
    ∃ u : (v.adicCompletionIntegers F)ˣ, ((u : v.adicCompletionIntegers F) : Fv F v) = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hx; exact zero_ne_one hx
  have hmem : x ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_eq hx)
  have hmem' : x⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hx, inv_one])
  refine ⟨⟨⟨x, hmem⟩, ⟨x⁻¹, hmem'⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_skew_unit_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (π : AE F E →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  intro F E _ _ _ _ _ σ h v π hπ
  obtain ⟨δ₀, h0, hs⟩ := cm_exists_skew σ h
  have ht : π (inclR (F := F) (AF F) δ₀) ≠ 0 :=
    (map_ne_zero_iff (π.comp (inclR (F := F) (AF F))) (RingHom.injective _)).2 h0
  have hF : ∀ f : F, π (inclR (F := F) (AF F) (algebraMap F E f)) = algebraMap F (Fv F v) f := by
    intro f
    have e1 : inclR (F := F) (AF F) (algebraMap F E f) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) f) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes f
    rw [e1, hπ, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  set t := π (inclR (F := F) (AF F) δ₀) with ht_def
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  refine ⟨algebraMap F E (ϖ ^ WithZero.log (Valued.v t)) * δ₀, ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes, hs]; ring
  · apply exists_unit_of_val_eq_one
    rw [map_mul, map_mul, hF, ← ht_def, map_mul]
    have e2 : Valued.v (algebraMap F (Fv F v) (ϖ ^ WithZero.log (Valued.v t))) =
        v.valuation F (ϖ ^ WithZero.log (Valued.v t)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [e2, map_zpow₀, hϖ]
    conv_lhs => rw [← WithZero.exp_log hvt]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp

end GlobalTheory.CMSkewUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugatePlaceCmField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlace

theorem conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) :
    GlobalTheory.SW.conjI P = P.map (IsCMField.ringOfIntegersComplexConj E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map, Set.image]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩

theorem exists_conj_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D PP
  let σ := IsCMField.ringOfIntegersComplexConj D.host.E
  haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ
  have hne : PP.asIdeal.map σ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]
    exact PP.ne_bot
  refine ⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩
  intro c hc
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv σ c).1 hc
  refine ⟨b, hb, ?_⟩
  show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact (IsCMField.complexConj_apply_apply D.host.E _).symm

end GlobalTheory.ConjPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameChangeWeakWeilRepresentation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem isThetaFunO_reF (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ (reS S b) T (reF S T b f) where
  quasi γ w := by
    show f (reW S T b (ratW T (reS S b) γ + w)) = ψ (-(symplOH (reS S b) T (ratW T (reS S b) γ) w)) * f (reW S T b w)
    rw [reW_add, ← symplOH_reW, reW_ratW S T b γ]
    exact hf.quasi _ _
  level := by
    obtain ⟨U, hU, hfU⟩ := hf.level
    refine ⟨U.comap (reWAdd S T b), hU.preimage (reW_continuous S T b), fun u hu hu0 => ?_⟩
    rw [heisO_reF]
    exact congrArg (reF S T b) (hfU _ hu ((reW_map_eq_zero S T b _ u).2 hu0))
  cont := hf.cont.comp (reW_continuous S T b)
  smooth k L hL hL0 w := by
    have := hf.smooth k ((reWAdd S T b).comp L) ((reW_continuous S T b).comp hL)
      (fun t => (reW_map_eq_zero S T b _ (L t)).2 (hL0 t)) (reW S T b w)
    have e : (fun t => reF S T b f (w + L t)) = fun t => f (reW S T b w + (reWAdd S T b).comp L t) :=
      funext fun t => by rw [reF_apply, reW_add]; rfl
    rw [e]; exact this

theorem isThetaFunO_of_reF (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ (reS S b) T (reF S T b f)) : IsThetaFunO ψ S T f := by
  have h := isThetaFunO_reF (reS S b) T S.frame ψ _ hf
  have e : reF (reS S b) T S.frame (reF S T b f) = f := by
    funext x
    exact congrArg f (reW_reWinv S T b x)
  rw [e] at h
  exact h

section Meas

theorem reW_fd (μ : Measure (WO (reS S b) T)) (𝓕 : Set (WO (reS S b) T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T (reS S b)) 𝓕 μ) :
    (μ.map (reW S T b)).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL T S) (reWinv S T b ⁻¹' 𝓕) (μ.map (reW S T b)) := by
  have hTR : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : BorelSpace (WO (reS S b) T) := ⟨rfl⟩
  let eA : WO (reS S b) T ≃+ WO S T :=
    { toFun := reW S T b
      invFun := reWinv S T b
      left_inv := reWinv_reW S T b
      right_inv := reW_reWinv S T b
      map_add' := reW_add S T b }
  let eM : WO (reS S b) T ≃ᵐ WO S T := (reWHomeo S T b).toMeasurableEquiv
  refine ⟨AddEquiv.isAddHaarMeasure_map μ eA (reW_continuous S T b) (reWinv_continuous S T b), ?_⟩
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL T (reS S b) → ratL T S := fun g => ⟨reW S T b g, (mem_ratL_reW S T b _).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨reWinv S T b g, (mem_ratL_reW S T b _).1 (by rw [reW_reWinv]; exact g.2)⟩, ?_⟩⟩
    · have e := congrArg (fun x : ratL T S => reWinv S T b (x : WO S T)) hg
      simp only [eG, reWinv_reW] at e
      exact Subtype.ext e
    · exact Subtype.ext (reW_reWinv S T b _)
  refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
  show reWinv S T b (reW S T b g + x) = (g : WO (reS S b) T) + reWinv S T b x
  rw [reWinv_add, reWinv_reW]

theorem setLIntegral_reW (μ : Measure (WO (reS S b) T)) (𝓕 : Set (WO (reS S b) T))
    (F : WO S T → ENNReal) :
    ∫⁻ w in 𝓕, F (reW S T b w) ∂μ = ∫⁻ x in reWinv S T b ⁻¹' 𝓕, F x ∂(μ.map (reW S T b)) := by
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : BorelSpace (WO (reS S b) T) := ⟨rfl⟩
  let eM : WO (reS S b) T ≃ᵐ WO S T := (reWHomeo S T b).toMeasurableEquiv
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have e1 := hmp.setLIntegral_comp_preimage_emb eM.measurableEmbedding F (reWinv S T b ⁻¹' 𝓕)
  have hpre : eM ⁻¹' (reWinv S T b ⁻¹' 𝓕) = 𝓕 := by
    ext w
    show reWinv S T b (reW S T b w) ∈ 𝓕 ↔ w ∈ 𝓕
    rw [reWinv_reW]
  rw [hpre] at e1
  exact e1

end Meas

section Weil

def omRe (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ) where
  toFun p := (reFEquiv S T b).toLinearMap ∘ₗ om (reGrp S b p.1, p.2) ∘ₗ (reFEquiv S T b).symm.toLinearMap
  map_one' := by
    ext f x
    show (reFEquiv S T b) ((om (reGrp S b 1, 1)) ((reFEquiv S T b).symm f)) x = f x
    rw [map_one, Prod.mk_one_one, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' p q := by
    ext f x
    simp [Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]

theorem omRe_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D (reS S b)) (g : GA D T)
    (f' : WO (reS S b) T → ℂ) :
    omRe S T b om (h, g) f' = reF S T b (om (reGrp S b h, g) ((reFEquiv S T b).symm f')) := rfl

theorem omRe_reF (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D (reS S b)) (g : GA D T)
    (f : WO S T → ℂ) : omRe S T b om (h, g) (reF S T b f) = reF S T b (om (reGrp S b h, g) f) := by
  have e : (reFEquiv S T b).symm (reF S T b f) = f := (reFEquiv S T b).symm_apply_apply f
  rw [omRe_apply, e]

theorem reF_symm (f' : WO (reS S b) T → ℂ) : reF S T b ((reFEquiv S T b).symm f') = f' :=
  (reFEquiv S T b).apply_symm_apply f'

theorem isWeak_omRe (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (hom : IsWeak ψ S T om) : IsWeak ψ (reS S b) T (omRe S T b om) where
  om_pres p f' hf' := by
    obtain ⟨h, g⟩ := p
    rw [omRe_apply]
    refine isThetaFunO_reF S T b ψ _ (hom.om_pres _ _ (isThetaFunO_of_reF S T b ψ _ ?_))
    rw [reF_symm]; exact hf'
  om_heis h g w₀ f' hf' := by
    set f := (reFEquiv S T b).symm f' with hf
    have hf1 : f' = reF S T b f := (reF_symm S T b f').symm
    have hth : IsThetaFunO ψ S T f := isThetaFunO_of_reF S T b ψ _ (by rw [← hf1]; exact hf')
    rw [hf1, heisO_reF, omRe_reF, omRe_reF, hom.om_heis _ _ _ _ hth, ← reW_actO, heisO_reF]
  om_aut γ hγ γ' hγ' f' hf' := by
    have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
      isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
    rw [omRe_apply, reF_apply, reW_zero, hom.om_aut _ (reGrp_mem_GQ S b γ hγ) _ hγ' _ hth]
    conv_rhs => rw [← reF_symm S T b f']
    exact (reF_zero b _).symm
  om_unit μ 𝓕 hμ h𝓕 p f' hf' := by
    obtain ⟨h, g⟩ := p
    have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
      isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
    obtain ⟨hν, h𝓕'⟩ := reW_fd S T b μ 𝓕 hμ h𝓕
    have e1 := setLIntegral_reW S T b μ 𝓕 fun x => ‖om (reGrp S b h, g) ((reFEquiv S T b).symm f') x‖ₑ ^ 2
    have e2 := setLIntegral_reW S T b μ 𝓕 fun x => ‖(reFEquiv S T b).symm f' x‖ₑ ^ 2
    have e3 := hom.om_unit _ _ hν h𝓕' (reGrp S b h, g) _ hth
    have e4 : (fun w => ‖f' w‖ₑ ^ 2) = fun w => ‖(reFEquiv S T b).symm f' (reW S T b w)‖ₑ ^ 2 := by
      funext w
      conv_lhs => rw [← reF_symm S T b f']
      rfl
    rw [e4]
    exact e1.trans (e3.trans e2.symm)

theorem contT_omRe (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (hc : ContT ψ om) : ContT ψ (omRe S T b om) := by
  intro f' hf' w
  have hth : IsThetaFunO ψ S T ((reFEquiv S T b).symm f') :=
    isThetaFunO_of_reF S T b ψ _ (by rw [reF_symm]; exact hf')
  have e : (fun g : GA D T => omRe S T b om (1, g) f' w) =
      fun g => om (1, g) ((reFEquiv S T b).symm f') (reW S T b w) := by
    funext g
    rw [omRe_apply, reF_apply, map_one]
  rw [e]
  exact hc _ hth _

end Weil

theorem reframe_weil : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V),
    ∃ e : GA D (reS S b) ≃* GA D S, (∀ h, e h ∈ GinfC S ↔ h ∈ GinfC (reS S b)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
        IsWeak ψ S T om → ContT ψ om →
        ∃ om' : GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ),
          IsWeak ψ (reS S b) T om' ∧ ContT ψ om' ∧
            ∀ h g f, om' (h, g) (reF S T b f) = reF S T b (om (e h, g) f) := by
  intro D S T b
  exact ⟨reGrp S b, reGrp_mem_GinfC S b, fun ψ om hom hc =>
    ⟨omRe S T b om, isWeak_omRe S T b ψ om hom, contT_omRe S T b ψ om hc, fun h g f => omRe_reF S T b om h g f⟩⟩

end GlobalTheory.AdSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfLatticeAdjointFrameReductionsEq
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjRedOnto

open Formalism.IndefR.Datum GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

theorem exists_half_redM_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ z : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
  ∃ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = z PP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io _ e he z
  have he2 := idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ R.Pg ∪ R.Q t, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' (hPP' : PP' ∈ R.Pg ∪ R.Q t),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : Formalism.L2.DIV.Pl D.host.E) (j : Fin (Vc D i).rank) (k : Fin (Wc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.asIdeal) (z PP j k)
  set L : Formalism.L2.DIV.Pl D.host.E → Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (Formalism.IndefR.Datum.EAf D) :=
    fun PP j k => ((Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) with hL
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) he2
    (∑ PP ∈ R.Pg ∪ R.Q t, toEAf D (es PP) • L PP)
  have hent : ∀ j k, frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x j k =
      ((⟨toEAf D e, hi⟩ * ∑ PP ∈ (R.Pg ∪ R.Q t).attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP.1 j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
    intro j k
    rw [hx', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Subring.coe_mul, AddSubmonoidClass.coe_finset_sum]
    congr 1
    rw [← Finset.sum_attach]
    rfl
  refine ⟨x, hx, fun j k => ?_, fun PP hPP => ?_⟩
  · rw [hent]; exact Subtype.prop _
  · funext j k
    unfold redM
    rw [dif_pos (by rw [hent]; exact Subtype.prop _)]
    have hsub : (⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x j k, by rw [hent]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D e, hi⟩ * ∑ PP ∈ (R.Pg ∪ R.Q t).attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP.1 j k) := Subtype.ext (hent j k)
    rw [hsub, RingHom.map_mul, hres PP hPP, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single ⟨PP, hPP⟩]
    · rw [hdel PP hPP PP hPP, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP hPP b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end GlobalTheory.AdjRedOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieAlgebraExpEqOfCommuteCartanInvolutionStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieAlgebra_exp_eq_of_commute_cartanInvolution : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C → ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  first | exact @GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan | exact GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan | (intros; apply GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  first | exact @GlobalTheory.ArchSlice.exists_schwartz_slice | exact GlobalTheory.ArchSlice.exists_schwartz_slice | (intros; apply GlobalTheory.ArchSlice.exists_schwartz_slice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivative
section
open MeasureTheory

namespace GlobalTheory

open LineDeriv

theorem dHeis_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))
  have hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ)) := L.hasTemperateGrowth
  refine ⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩
  intro x
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnramifiedExponentOfIwahoriFixedVectorStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_of_iwahori_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → fixed π (iwahori k (Fin n)) ≠ ⊥ → ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  first | exact @GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | exact GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | (intros; apply GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevMov

theorem finE_mem_St_of_isMov : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  intro D V L β hβ k hk
  have h1 := GlobalTheory.LevSplit.mem_St_iff β L hβ (Lev.finE V k)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff L) (finHom V k)
  refine h1.2 (h2.1 ?_)
  have hk' : ∀ u, u ∈ hatV L ↔ ∃ u₀ ∈ hatV L, u = (finHom V k).1 *ᵥ u₀ := hk
  intro y
  constructor
  · intro hy
    exact (hk' _).2 ⟨y, hy, rfl⟩
  · intro hy
    obtain ⟨u₀, hu₀, e⟩ := (hk' _).1 hy
    have e2 : y = u₀ := by
      have := congrArg (fun z => ((finHom V k)⁻¹).1 *ᵥ z) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
      exact this
    rw [e2]; exact hu₀

end GlobalTheory.LevMov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModelStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  first | exact @GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel | exact GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel | (intros; apply GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormulaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridParameter_regular_card_eq_rankFormula : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parD i j) ∧ ((GlobalTheory.Grid.grid D τ).parD i j).card = GlobalTheory.Grid.rkV D i j := by
  first | exact @GlobalTheory.GridParDCount.parD_regular_card | exact GlobalTheory.GridParDCount.parD_regular_card | (intros; apply GlobalTheory.GridParDCount.parD_regular_card <;> assumption)
end


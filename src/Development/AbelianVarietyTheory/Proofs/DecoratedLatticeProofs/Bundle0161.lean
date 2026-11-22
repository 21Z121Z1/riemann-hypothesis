import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilVacuumLocalModelIntegralMatrixPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedKFiniteFiniteDimensional
section
open scoped NNReal
open GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.EisCont

def transComb {G : Type} [Group G] (K : Subgroup G) (ψ : G → ℂ) : (K →₀ ℂ) →ₗ[ℂ] (G → ℂ) :=
  Finsupp.lsum ℂ fun k : K => LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (fun g => ψ (g * k))

theorem transComb_apply {G : Type} [Group G] (K : Subgroup G) (ψ : G → ℂ) (c : K →₀ ℂ) (g : G) :
    transComb K ψ c g = c.sum fun k z => z * ψ (g * k) := by
  simp [transComb, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]

def domSub {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
    (φ : G → ℂ) : Submodule ℂ (G → ℂ) where
  carrier := domSet δ K χ t φ
  zero_mem' := ⟨fun _ _ => by simp, fun c _ g => by simp [Finsupp.sum]⟩
  add_mem' := fun {a b} ha hb => ⟨fun p g => by simp only [Pi.add_apply, ha.1 p g, hb.1 p g, mul_add],
    fun c hc g => by
      have h1 := ha.2 c hc g
      have h2 := hb.2 c hc g
      simp only [Pi.add_apply, mul_add]
      rw [Finsupp.sum_add, h1, h2, add_zero]⟩
  smul_mem' := fun a b hb => ⟨fun p g => by simp only [Pi.smul_apply, hb.1 p g, smul_eq_mul]; ring,
    fun c hc g => by
      have h1 := hb.2 c hc g
      simp only [Pi.smul_apply, smul_eq_mul]
      have : (c.sum fun k z => z * (a * b (g * k))) = a * c.sum fun k z => z * b (g * k) := by
        rw [Finsupp.mul_sum]; congr 1; ext k z; ring
      rw [this, h1, mul_zero]⟩

theorem span_domSet_le {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle)
    (t : ℂ) (φ : G → ℂ) : Submodule.span ℂ (domSet δ K χ t φ) ≤ domSub δ K χ t φ :=
  Submodule.span_le.2 fun _ h => h

theorem range_transComb_le {G : Type} [Group G] (K : Subgroup G) (φ : G → ℂ) :
    LinearMap.range (transComb K φ) ≤ kSpan K φ := by
  rintro _ ⟨c, rfl⟩
  have : transComb K φ c = c.sum fun k z => z • fun g => φ (g * k) := by
    ext g; rw [transComb_apply]; simp [Finsupp.sum, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i : G), i.2, rfl⟩)

def evalForm {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
    (φ : G → ℂ) : domSub δ K χ t φ →ₗ[ℂ] ((K →₀ ℂ) ⧸ LinearMap.ker (transComb K φ)) →ₗ[ℂ] ℂ where
  toFun ψ := (LinearMap.ker (transComb K φ)).liftQ ((LinearMap.proj 1).comp (transComb K ψ)) (by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := ψ.2.2 c (fun g => by rw [← transComb_apply, hc]; rfl) 1
    simpa [transComb_apply] using this)
  map_add' a b := by
    ext c
    simp [transComb_apply, Finsupp.sum_add, mul_add]
  map_smul' a b := by
    ext c
    simp only [transComb_apply, LinearMap.comp_apply, Submodule.liftQ_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, LinearMap.proj_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      LinearMap.smul_apply, Finsupp.mul_sum]
    congr 1; ext k z; ring

theorem evalForm_injective {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle)
    (t : ℂ) (φ : G → ℂ) (hPK : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : Function.Injective (evalForm δ K χ t φ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  apply Subtype.ext
  refine IndLaw.ext hPK ψ.2.1 (fun _ _ => by simp) fun k hk => ?_
  have := LinearMap.congr_fun hψ (Submodule.mkQ _ (Finsupp.single ⟨k, hk⟩ 1))
  simpa [evalForm, transComb_apply] using this

theorem finiteDimensional_span_domSet : ∀ (G : Type) [Group G] (P K : Subgroup G) (δ : P →* ℝ≥0) (χ : P →* Circle)
    (t : ℂ) (φ : G → ℂ), (∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) → IsKFinite K φ →
    FiniteDimensional ℂ (Submodule.span ℂ (domSet δ K χ t φ)) := by
  intro G _ P K δ χ t φ hPK hφ
  haveI : FiniteDimensional ℂ (kSpan K φ) := hφ
  have : FiniteDimensional ℂ (LinearMap.range (transComb K φ)) :=
    Submodule.finiteDimensional_of_le (range_transComb_le K φ)
  have : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker (transComb K φ)) :=
    LinearEquiv.finiteDimensional (transComb K φ).quotKerEquivRange.symm
  have : FiniteDimensional ℂ (domSub δ K χ t φ) :=
    Module.Finite.of_injective _ (evalForm_injective δ K χ t φ hPK)
  exact Submodule.finiteDimensional_of_le (span_domSet_le δ K χ t φ)

end GlobalTheory.EisCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainFlagUnipotentCoords
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.ThreeLayers

section Abstract

open scoped Pointwise

variable {A B U X G : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B] [MeasurableSpace B]
  [Group U] [MeasurableSpace U] [MeasurableSpace X] [Group G] [MulAction G X]
  {mA : Measure A} {mB : Measure B} {ν : Measure U} [SFinite mA] [SFinite mB] [SFinite ν]

omit [AddCommGroup A] [MeasurableAdd₂ A] [AddGroup B] [Group U] in

theorem null_last {N : Set U} (hN : ν N = 0) : (mA.prod (mB.prod ν)) {p | p.2.2 ∈ N} = 0 := by
  have h : {p : A × (B × U) | p.2.2 ∈ N} = Set.univ ×ˢ (Set.univ ×ˢ N) := by
    ext p; simp
  rw [h, Measure.prod_prod, Measure.prod_prod, hN]
  simp

omit [AddCommGroup A] [MeasurableAdd₂ A] [AddGroup B] [Group U] in

theorem null_mid {β : B → B} (hβ : Measure.QuasiMeasurePreserving β mB mB) {N : Set B} (hN : mB N = 0) :
    (mA.prod (mB.prod ν)) {p | β p.2.1 ∈ N} = 0 := by
  have h : {p : A × (B × U) | β p.2.1 ∈ N} = Set.univ ×ˢ ((β ⁻¹' N) ×ˢ Set.univ) := by
    ext p; simp
  rw [h, Measure.prod_prod, Measure.prod_prod, hβ.preimage_null hN]
  simp

omit [AddGroup B] [Group U] in

theorem null_first [mA.IsAddLeftInvariant] {α : A → A} (hα : Measure.QuasiMeasurePreserving α mA mA) {φ : B → A}
    (hφ : Measurable φ) {N : Set A} (hN : mA N = 0) :
    (mA.prod (mB.prod ν)) {p | α p.1 + φ p.2.1 ∈ N} = 0 := by
  have hM : MeasurableSet (toMeasurable mA N) := measurableSet_toMeasurable _ _
  have hM0 : mA (toMeasurable mA N) = 0 := by rw [measure_toMeasurable, hN]
  have hs : MeasurableSet {p : A × (B × U) | α p.1 + φ p.2.1 ∈ toMeasurable mA N} :=
    ((hα.measurable.comp measurable_fst).add (hφ.comp (measurable_fst.comp measurable_snd))) hM
  refine measure_mono_null (t := {p : A × (B × U) | α p.1 + φ p.2.1 ∈ toMeasurable mA N})
    (fun p hp => subset_toMeasurable mA N hp) ?_
  rw [Measure.prod_apply_symm hs]
  have h0 : ∀ y : B × U, mA ((fun x => (x, y)) ⁻¹' {p : A × (B × U) | α p.1 + φ p.2.1 ∈ toMeasurable mA N}) = 0 := fun y => by
    have h1 : (fun x : A => (x, y)) ⁻¹' {p : A × (B × U) | α p.1 + φ p.2.1 ∈ toMeasurable mA N} =
        α ⁻¹' ((fun x => φ y.1 + x) ⁻¹' toMeasurable mA N) := by
      ext x; simp [add_comm]
    rw [h1]
    exact hα.preimage_null (by rw [measure_preimage_add, hM0])
  exact (lintegral_congr h0).trans lintegral_zero

theorem isFundamentalDomain_three [mA.IsAddLeftInvariant] (ΓA : AddSubgroup A) (ΓB : AddSubgroup B) (ΓU : Subgroup U)
    [Countable ΓB] [Countable ΓU] (α : U → A → A) (β : U → B → B)
    (hα : ∀ u, Measure.QuasiMeasurePreserving (α u) mA mA) (hβ : ∀ u, Measure.QuasiMeasurePreserving (β u) mB mB)
    (κ : B → B → A) (hκ : ∀ b', Measurable (κ b')) (e : A × (B × U) ≃ᵐ X)
    (hfree : ∀ (g g' : G) (x : X), g • x = g' • x → g = g')
    (hG : ∀ g : G, ∃ (c' : ΓA) (b' : ΓB) (u' : ΓU), ∀ p,
      g • e p = e (c'.1 + α u'.1 p.1 + κ b'.1 (β u'.1 p.2.1), b'.1 + β u'.1 p.2.1, u'.1 * p.2.2))
    (hG' : ∀ (c' : ΓA) (b' : ΓB) (u' : ΓU), ∃ g : G, ∀ p,
      g • e p = e (c'.1 + α u'.1 p.1 + κ b'.1 (β u'.1 p.2.1), b'.1 + β u'.1 p.2.1, u'.1 * p.2.2))
    {𝓒 : Set A} {𝓕 : Set B} {𝓤 : Set U} (hC : IsAddFundamentalDomain ΓA 𝓒 mA) (hF : IsAddFundamentalDomain ΓB 𝓕 mB)
    (hU : IsFundamentalDomain ΓU 𝓤 ν) :
    IsFundamentalDomain G (e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤))) ((mA.prod (mB.prod ν)).map e) := by
  have hmem : ∀ q, e q ∈ e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤)) ↔ q ∈ 𝓒 ×ˢ (𝓕 ×ˢ 𝓤) :=
    fun q => e.injective.mem_set_image
  have hmp := (e.measurable.measurePreserving (mA.prod (mB.prod ν))).symm e
  have hφ : ∀ (b' : B) (u : U), Measurable fun b => κ b' (β u b) := fun b' u => (hκ b').comp (hβ u).measurable
  refine ⟨?_, ?_, ?_⟩
  · have hS : NullMeasurableSet (𝓒 ×ˢ (𝓕 ×ˢ 𝓤)) (mA.prod (mB.prod ν)) :=
      hC.nullMeasurableSet.prod (hF.nullMeasurableSet.prod hU.nullMeasurableSet)
    rw [e.image_eq_preimage_symm]
    exact hS.preimage hmp.quasiMeasurePreserving
  · rw [e.measurableEmbedding.ae_map_iff]
    have h0 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∃ g : ΓU, g • p.2.2 ∈ 𝓤 :=
      ae_iff.2 (null_last (mA := mA) (mB := mB) (ae_iff.1 hU.ae_covers))
    have h1 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∀ u' : ΓU, ∃ g : ΓB, g +ᵥ β u'.1 p.2.1 ∈ 𝓕 := by
      rw [ae_all_iff]
      intro u'
      exact ae_iff.2 (null_mid (mA := mA) (ν := ν) (hβ u'.1) (ae_iff.1 hF.ae_covers))
    have h2 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∀ (u' : ΓU) (b' : ΓB), ∃ g : ΓA,
        g +ᵥ (α u'.1 p.1 + κ b'.1 (β u'.1 p.2.1)) ∈ 𝓒 := by
      rw [ae_all_iff]
      intro u'
      rw [ae_all_iff]
      intro b'
      exact ae_iff.2 (null_first (ν := ν) (hα u'.1) (hφ b'.1 u'.1) (ae_iff.1 hC.ae_covers))
    filter_upwards [h0, h1, h2] with p hp0 hp1 hp2
    obtain ⟨u', hu⟩ := hp0
    obtain ⟨b', hb⟩ := hp1 u'
    obtain ⟨c', hc⟩ := hp2 u' b'
    obtain ⟨g, hg⟩ := hG' c' b' u'
    refine ⟨g, ?_⟩
    rw [hg p, hmem]
    refine ⟨?_, hb, hu⟩
    rw [AddSubgroup.vadd_def, vadd_eq_add] at hc
    simpa only [add_assoc] using hc
  · intro g₁ g₂ hne
    obtain ⟨c₁, b₁, u₁, h₁⟩ := hG g₁⁻¹
    obtain ⟨c₂, b₂, u₂, h₂⟩ := hG g₂⁻¹
    change (mA.prod (mB.prod ν)).map e (g₁ • (e '' _) ∩ g₂ • (e '' _)) = 0
    rw [e.map_apply]
    have hin : ∀ p, p ∈ e ⁻¹' (g₁ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤))) ∩ g₂ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ 𝓤)))) →
        (c₁.1 + α u₁.1 p.1 + κ b₁.1 (β u₁.1 p.2.1) ∈ 𝓒 ∧ b₁.1 + β u₁.1 p.2.1 ∈ 𝓕 ∧ u₁.1 * p.2.2 ∈ 𝓤) ∧
        (c₂.1 + α u₂.1 p.1 + κ b₂.1 (β u₂.1 p.2.1) ∈ 𝓒 ∧ b₂.1 + β u₂.1 p.2.1 ∈ 𝓕 ∧ u₂.1 * p.2.2 ∈ 𝓤) := by
      rintro p ⟨hp1, hp2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₁, hmem] at hp1
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₂, hmem] at hp2
      exact ⟨⟨hp1.1, hp1.2.1, hp1.2.2⟩, ⟨hp2.1, hp2.2.1, hp2.2.2⟩⟩
    by_cases hu : u₁ = u₂
    · subst hu
      by_cases hb : b₁ = b₂
      · subst hb
        by_cases hc : c₁ = c₂
        · subst hc
          refine measure_mono_null (t := ∅) (fun p hp => ?_) (measure_empty)
          have : g₁⁻¹ • e p = g₂⁻¹ • e p := by rw [h₁, h₂]
          exact absurd (inv_injective (hfree _ _ _ this)) hne
        · have hd := hC.aedisjoint (i := -c₁) (j := -c₂) (fun h => hc (neg_injective h))
          have hd' : mA ((-c₁ +ᵥ 𝓒) ∩ (-c₂ +ᵥ 𝓒)) = 0 := hd
          refine measure_mono_null (fun p hp => ?_) (null_first (hα u₁.1) (hφ b₁.1 u₁.1) hd')
          obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hin p hp
          refine ⟨?_, ?_⟩
          · rw [Set.mem_neg_vadd_set_iff]
            simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h1
          · rw [Set.mem_neg_vadd_set_iff]
            simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h2
      · have hd := hF.aedisjoint (i := -b₁) (j := -b₂) (fun h => hb (neg_injective h))
        have hd' : mB ((-b₁ +ᵥ 𝓕) ∩ (-b₂ +ᵥ 𝓕)) = 0 := hd
        refine measure_mono_null (fun p hp => ?_) (null_mid (mA := mA) (ν := ν) (hβ u₁.1) hd')
        obtain ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩ := hin p hp
        exact ⟨Set.mem_neg_vadd_set_iff.2 h1, Set.mem_neg_vadd_set_iff.2 h2⟩
    · have hd := hU.aedisjoint (i := u₁⁻¹) (j := u₂⁻¹) (fun h => hu (inv_injective h))
      have hd' : ν ((u₁⁻¹ • 𝓤) ∩ (u₂⁻¹ • 𝓤)) = 0 := hd
      refine measure_mono_null (fun p hp => ?_) (null_last (mA := mA) (mB := mB) hd')
      obtain ⟨⟨-, -, h1⟩, ⟨-, -, h2⟩⟩ := hin p hp
      exact ⟨Set.mem_inv_smul_set_iff.2 h1, Set.mem_inv_smul_set_iff.2 h2⟩

end Abstract

theorem act_coords {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c' c : skewA D ρ) (b' b : Mx D ρ S₀.rank)
    (u' u : GL (Fin ρ) (AE D)) :
    d.nC c' * (d.nB b' * d.levi u') * (d.nC c * (d.nB b * d.levi u)) =
      d.nC (c' + skewConj u'.1 c + cComm S₀ b' (u'.1 ⬝ b)) * (d.nB (b' + u'.1 ⬝ b) * d.levi (u' * u)) := by
  rw [← GlobalTheory.Layers.act_coords, map_mul]
  calc d.nC c' * (d.nB b' * d.levi u') * (d.nC c * (d.nB b * d.levi u))
      = d.nC c' * d.nB b' * ((d.levi u' * d.nC c) * (d.nB b * d.levi u)) := by simp only [mul_assoc]
    _ = d.nC c' * d.nB b' * (d.nC (skewConj u'.1 c) * ((d.levi u' * d.nB b) * d.levi u)) := by
        rw [d.levi_mul_nC]; simp only [mul_assoc]
    _ = _ := by rw [d.levi_mul_nB]; simp only [mul_assoc]

theorem fundDomain_coords : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)) (𝓤 : Set (UX D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → IsFundamentalDomain (UXQ D ρ) 𝓤 vU.ν → IsFundamentalDomain (NFlagQ V d.e) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ 𝓤))) ((lC.prod (vb.μ.prod vU.ν)).map e) := by
  intro D V V₀ ρ d vb vU e he lC 𝓒 𝓤 hlC _ hC hU
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).1
  haveI : LocallyCompactSpace (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.1
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.2.2.1
  haveI : Countable (ratMx D ρ V₀.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  haveI hca : ContinuousAdd (skewA D ρ) := IsTopologicalAddGroup.toContinuousAdd
  haveI : MeasurableAdd₂ (skewA D ρ) := @ContinuousAdd.measurableMul₂ (skewA D ρ) _ _ _ _ _ hca
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : Countable (UXQ D ρ) := (GlobalTheory.UnitU.rational D ρ).1
  haveI := vU.unit.1
  haveI := vb.covol.1
  haveI : SigmaFinite vb.μ := inferInstance
  haveI : SigmaFinite vU.ν := inferInstance
  have hκ : ∀ b' : Mx D ρ V₀.rank, Measurable (cComm V₀ b') := by
    intro b'
    have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
    have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
    have h1 : Continuous fun b : Mx D ρ V₀.rank => half D • (b ⬝ plus V₀ b' - b' ⬝ plus V₀ b) :=
      ((continuous_id.matrix_mul continuous_const).sub (continuous_const.matrix_mul hp)).const_smul (half D)
    exact (h1.subtype_mk _).measurable
  have key : ∀ (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) (u' : UX D ρ) (p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ)),
      d.nC c' * (d.nB b' * d.levi u'.1) * (e p : GA D V) =
        (e (c' + skewConj u'.1.1 p.1 + cComm V₀ b' (u'.1.1 ⬝ p.2.1), b' + u'.1.1 ⬝ p.2.1, u' * p.2.2) : GA D V) := by
    intro c' b' u' p
    rw [he p, he (c' + skewConj u'.1.1 p.1 + cComm V₀ b' (u'.1.1 ⬝ p.2.1), b' + u'.1.1 ⬝ p.2.1, u' * p.2.2)]
    exact act_coords d c' p.1 b' p.2.1 u'.1 p.2.2.1
  have hsm : ∀ (g : NFlagQ V d.e) (x : flagN d),
      ((g • x : flagN d) : GA D V) = ((g : flagN d) : GA D V) * (x : GA D V) := fun _ _ => rfl
  refine isFundamentalDomain_three (mA := lC) (mB := vb.μ) (ν := vU.ν) ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ))
    (ratMx D ρ V₀.rank) (UXQ D ρ) (fun u => skewConj u.1.1) (fun u b => u.1.1 ⬝ b)
    (GlobalTheory.T.quasiMeasurePreserving_skewHermitianCongruence_unitriangular D ρ lC hlC) (GlobalTheory.T.quasiMeasurePreserving_adelicUnitriangular_left_mul D ρ V₀.rank vb.μ vb.covol.1) (cComm V₀) hκ e ?_ ?_ ?_ hC vb.covol.2.1 hU
  · intro g g' x h
    rw [Subgroup.smul_def, Subgroup.smul_def] at h
    exact Subtype.ext (mul_right_cancel h)
  · intro g
    obtain ⟨c, b, u, hg, hc, hb, hu⟩ := GlobalTheory.T.exists_rational_wittFlagCoordinates_of_mem_unipotent D V V₀ ρ d g.1.1 (Subgroup.mem_subgroupOf.1 g.2) g.1.2
    refine ⟨⟨c, AddSubgroup.mem_addSubgroupOf.2 hc⟩, ⟨b, hb⟩, ⟨u, hu⟩, fun p => Subtype.ext ?_⟩
    rw [hsm, hg]
    exact key c b u p
  · rintro ⟨c', hc'⟩ ⟨b', hb'⟩ ⟨u', hu'⟩
    have hQ : d.nC c' * (d.nB b' * d.levi u'.1) ∈ GQ V :=
      mul_mem (d.nC_mem_GQ (AddSubgroup.mem_addSubgroupOf.1 hc')) (mul_mem (d.nB_mem_GQ hb') (d.levi_mem_GQ hu'.1 hu'.2))
    have h1 := he (c', b', u')
    let g : NFlagQ V d.e := ⟨e (c', b', u'), Subgroup.mem_subgroupOf.2 (by rw [h1]; exact hQ)⟩
    refine ⟨g, fun p => Subtype.ext ((hsm g (e p)).trans ?_)⟩
    rw [show ((g : flagN d) : GA D V) = _ from h1]
    exact key c' b' u' p

end GlobalTheory.ThreeLayers

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineRowTranslationHeisenbergSplitPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineRowFrame

variable {D : D7}

theorem half_mul {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (v : Mx D m n) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu i]

theorem mul_half {e : AE D} {l m n : ℕ} (u : Mx D l m) {v : Mx D m n} (hv : IsHalf e v) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hv a j]

theorem adj_half {e : AE D} {m n : ℕ} {u : Mx D m n} (hu : IsHalf e u) : IsHalf (cA D e) (adj u) := fun i j => by
  change cA D e * cA D (u j i) = cA D (u j i)
  rw [← map_mul, hu j i]

theorem ofAdj_half {e : AE D} (S T : HSp D) {z : Mx D S.rank T.rank} (hz : IsHalf e z) :
    IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) := fun i j => by
  have h := mul_half (giA T) (half_mul (adj_half hz) (gA S)) i j
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.smul_apply, smul_eq_mul, mul_left_comm, h]

theorem xi_mul_hO (S T : HSp D) (x : WO S T) (z : Mx D S.rank T.rank) :
    incA D D.host.xi0 * hO S T x (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) = (z ⬝ x).trace := by
  conv_rhs => rw [← GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj S T z]
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem incA_mul_ι (a : D.host.E) (x : k) : incA D a * p.ι x = p.ι (p.pr a * x) := by
  conv_rhs => rw [← p.π_ι x, Place.pr, ← map_mul, p.ι_π, mul_left_comm, Witness.e_ι]

theorem pr_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) (r : Fin m) :
    p.pr ((M *ᵥ v) r) = ∑ a, p.pr (M r a) * p.pr (v a) := by
  simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem line_row : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h₀ h₀' u₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  obtain ⟨w, hw⟩ : ∃ w, w = u₀ ᵥ* FS.γ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : WO S B'.L, ∀ a c, x a c = p.ι (s * p.xi * p.pr (B'.ζ a) * w c) :=
    ⟨Matrix.of fun a c => p.ι (s * p.xi * p.pr (B'.ζ a) * w c), fun _ _ => rfl⟩
  have hxh : IsHalf p.e x := fun a c => by rw [hx, Witness.e_ι]
  have hy : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  have hh : IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) := by
    rw [hy]
    exact half_mul (ofAdj_half B.L S (mul_half _ hxh)) _
  refine ⟨x, ?_, hh, fun t => ?_⟩
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    ext r c
    have e1 : (F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c = s * p.xi * p.pr (vecB B'.o B'.ζ r) * w c := by
      rw [Matrix.mul_assoc, fromRows_mul, Matrix.zero_mul, Matrix.mul_apply, Fintype.sum_sum_type, ← h₀'.2 r, hw]
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    change p.ι ((F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c) = _
    rw [e1, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx]
    change _ = incA D (B'.o.iB r a) * _
    rw [incA_mul_ι]
    congr 1
    ring
  · rw [(GlobalTheory.LocSympl.halves_at_split D k p _ _ B.V₀ S F₀ FS ψ ψk hk).2.2.2.1 t _ hh]
    congr 2
    rw [B.o.hO_resS, AddEquiv.apply_symm_apply, hO_eq_trace B.A, adj_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.trace_zero, zero_add]
    refine mul_left_cancel₀ hxi ?_
    have e2 : ∀ a c, p.π (((rat l.τ : Mx D B.L.rank B'.L.rank) ⬝ x) a c) = -(s * p.xi * w c) * p.pr (B.ζ a) := fun a c => by
      have h1 := pr_mulVec p l.τ B'.ζ a
      rw [l.map, Pi.neg_apply, Place.pr, map_neg, map_neg] at h1
      rw [Place.pr, neg_mul, ← mul_neg, h1, Matrix.mul_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hx, p.π_ι]
      change p.pr (l.τ a b) * _ = _
      ring
    have e3 : ∀ c a, p.π ((p.up F₀ FS t ⬝ B.o.jB) c a) = ∑ r, (FS.β * t * F₀.γ) c r * p.pr (B.o.iB r a) := fun c a => by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (p.π_ι _)
    have e4 : ∀ c, ∑ r, (FS.β * t * F₀.γ) c r * F₀.β r (Sum.inr ()) = (FS.β * t) c (Sum.inr ()) := fun c => by
      rw [← Matrix.mul_apply, Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
    have e5 : ∑ c, w c * (FS.β * t) c (Sum.inr ()) = u₀ ⬝ᵥ fun r => t r (Sum.inr ()) := by
      change (w ᵥ* (FS.β * t)) (Sum.inr ()) = (u₀ ᵥ* t) (Sum.inr ())
      rw [hw, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, FS.γβ, Matrix.one_mul]
    change p.π (incA D D.host.xi0) * p.π (hO B.L S (p.up F₀ FS t ⬝ B.o.jB) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S _)) = _
    rw [← map_mul, xi_mul_hO, Matrix.trace_mul_comm, ← e5, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, ← e4,
      Finset.sum_congr rfl fun a _ => (p.π.map_mul _ _).trans (congrArg₂ (· * ·) (e3 c a) (e2 a c))]
    generalize FS.β * t * F₀.γ = M
    simp only [h₀.2, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LineRowFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleStaStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  first | exact @GlobalTheory.TensorIrr.eq_top_of_stable | exact GlobalTheory.TensorIrr.eq_top_of_stable | (intros; apply GlobalTheory.TensorIrr.eq_top_of_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitaryStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α w → (∃ C : ℝ, ∀ g, ‖w g‖ ≤ C) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  first | exact @GlobalTheory.ZonalBound.trivialBound_of_bounded | exact GlobalTheory.ZonalBound.trivialBound_of_bounded | (intros; apply GlobalTheory.ZonalBound.trivialBound_of_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionOrthogonalSumApproxFiniteSumsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_orthogonal_sum_approx_finite_sums : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (P : Fin n → WO A T → ℂ) (g : Fin n → WO B T → ℂ), (∀ i, Continuous (P i)) ∧ (∀ i (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), P i (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * P i u) ∧ (∀ i, IsThetaFunO ψ B T (g i)) ∧ ∀ w, ‖f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε := by
  first | exact @GlobalTheory.ThetaSplitApprox.exists_approx | exact GlobalTheory.ThetaSplitApprox.exists_approx | (intros; apply GlobalTheory.ThetaSplitApprox.exists_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsDenseContinuousThetaLawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_functions_dense_continuous_theta_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  first | exact @GlobalTheory.HeisSmoothing.exists_theta_near | exact GlobalTheory.HeisSmoothing.exists_theta_near | (intros; apply GlobalTheory.HeisSmoothing.exists_theta_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilVacuumLocalModelIntegralMatrixPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_local_model_integral_matrix_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ), p.IsComp χS μS → p.IsComp χT μT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → Enl gk hk → ∃ Φ₀ Φ₀' : SB (Matrix Y Y' k), Φ₀ ≠ 0 ∧ Φ₀'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ₀.1 ∧ ω (g, h) (Tm Φ₀) = Tm Φ₀' := by
  first | exact @GlobalTheory.LocOm.vacuum_move | exact GlobalTheory.LocOm.vacuum_move | (intros; apply GlobalTheory.LocOm.vacuum_move <;> assumption)
end


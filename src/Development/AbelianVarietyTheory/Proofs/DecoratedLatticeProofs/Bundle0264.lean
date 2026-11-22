import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CellInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def dcos (R K : Subgroup G) (q : G) : Set G := {g | ∃ r ∈ R, ∃ k ∈ K, g = r * q * k}

theorem dcos_eq_of_mem {R K : Subgroup G} {q h : G} (hh : h ∈ dcos R K q) : dcos R K h = dcos R K q := by
  obtain ⟨r, hr, k, hk, rfl⟩ := hh
  ext g
  constructor
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r, R.mul_mem hr' hr, k * k', K.mul_mem hk hk', by group⟩
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r⁻¹, R.mul_mem hr' (R.inv_mem hr), k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', by group⟩

def cellSet (R K : Subgroup G) (q h : G) : Set R := {r | q⁻¹ * ((r : G) * h) ∈ K}

theorem isOpen_cellSet {R K : Subgroup G} (hK : IsOpen (K : Set G)) (q h : G) : IsOpen (cellSet R K q h) :=
  (continuous_const.mul (continuous_subtype_val.mul continuous_const)).isOpen_preimage _ hK

theorem isCompact_cellSet {R K : Subgroup G} (hR : IsClosed (R : Set G)) (hK : IsCompact (K : Set G)) (q h : G) :
    IsCompact (cellSet R K q h) := by
  have h1 : IsCompact ((fun x : G => q⁻¹ * (x * h)) ⁻¹' (K : Set G)) :=
    ((Homeomorph.mulRight h).trans (Homeomorph.mulLeft q⁻¹)).isCompact_preimage.2 hK
  exact hR.isClosedEmbedding_subtypeVal.isCompact_preimage h1

theorem cellSet_of_mem {R K : Subgroup G} {q h : G} (r0 : R) (k0 : G) (hk0 : k0 ∈ K) (hh : h = r0 * q * k0) :
    cellSet R K q h = (fun r => r * r0) ⁻¹' cellSet R K q q := by
  ext r
  simp only [cellSet, Set.mem_preimage, Set.mem_setOf_eq, Subgroup.coe_mul, hh]
  constructor
  · intro hr
    have := K.mul_mem hr (K.inv_mem hk0)
    convert this using 1; group
  · intro hr
    have := K.mul_mem hr hk0
    convert this using 1; group

theorem cellSet_eq_empty {R K : Subgroup G} {q h : G} (hh : h ∉ dcos R K q) : cellSet R K q h = ∅ :=
  Set.eq_empty_of_forall_notMem fun r hr =>
    hh ⟨(r : G)⁻¹, R.inv_mem r.2, q⁻¹ * ((r : G) * h), hr, by group⟩

open Classical in

theorem isQuotientIntegral_indicator_doubleCoset (R K : Subgroup G) (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (q : G) :
    IsQuotIntL1 ρ μ (fun g => if g ∈ dcos R K q then 1 else 0)
      (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) := by
  classical
  have hRI : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  set c : ℂ := ((((ρ (cellSet R K q q)).toReal)⁻¹ : ℝ) : ℂ) with hc
  set A : Set G := (fun x => q⁻¹ * x) ⁻¹' (K : Set G) with hA
  have hAo : IsOpen A := (continuous_const.mul continuous_id).isOpen_preimage _ hKo
  have hAc : IsCompact A := (Homeomorph.mulLeft q⁻¹).isCompact_preimage.2 hKc
  have hAμ : μ A = μ K := measure_preimage_mul μ q⁻¹ _
  have hS0 : ρ (cellSet R K q q) ≠ 0 := (isOpen_cellSet hKo q q).measure_ne_zero ρ ⟨1, by simp [cellSet]⟩
  have hSt : ρ (cellSet R K q q) ≠ ⊤ := ((isCompact_cellSet hR hKc q q).measure_lt_top (μ := ρ)).ne
  have e : ∀ h, (fun r : R => A.indicator (fun _ => c) ((r : G) * h)) = (cellSet R K q h).indicator fun _ => c := by
    intro h; funext r; simp only [Set.indicator_apply, hA, cellSet, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
  refine ⟨A.indicator fun _ => c, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrableOn_const hAc.measure_lt_top.ne).integrable_indicator hAo.measurableSet
  · rw [e h]
    exact (integrableOn_const ((isCompact_cellSet hR hKc q h).measure_lt_top (μ := ρ)).ne).integrable_indicator
      (isOpen_cellSet hKo q h).measurableSet
  · rw [e h, integral_indicator (isOpen_cellSet hKo q h).measurableSet, setIntegral_const]
    show (if h ∈ dcos R K q then (1 : ℂ) else 0) = ρ.real (cellSet R K q h) • c
    by_cases hh : h ∈ dcos R K q
    · rw [if_pos hh]
      obtain ⟨r0, hr0, k0, hk0, rfl⟩ := hh
      rw [cellSet_of_mem ⟨r0, hr0⟩ k0 hk0 rfl, measureReal_def, measure_preimage_mul_right, hc, Complex.real_smul,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hS0, hSt⟩), Complex.ofReal_one]
    · rw [if_neg hh, cellSet_eq_empty hh]
      simp
  · rw [integral_indicator hAo.measurableSet, setIntegral_const, measureReal_def, hAμ, hc, Complex.real_smul, ← Complex.ofReal_mul, div_eq_mul_inv]

theorem quotient_integral_finset_sum {R : Subgroup G} {ρ : Measure R} {μ : Measure G} {ι : Type} (s : Finset ι)
    (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.CellInt

open GlobalTheory.CellInt in

theorem GlobalTheory.CellInt.quotInt_finiteCells : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  intro G _ _ _ _ _ _ _ _ R K hR hKc hKo ρ μ hρ hρi hμ hμr T
  classical
  obtain ⟨u, hus, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := dcos R K) (T : Set G)
    (T.image (dcos R K)) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨u, fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ), Finset.coe_subset.1 hus,
    fun f hfR hfK hsupp => ?_⟩
  have hinv : ∀ q h, h ∈ dcos R K q → f h = f q := by
    rintro q h ⟨r, hr, k, hk, rfl⟩
    rw [mul_assoc, hfR r hr, hfK k hk]
  have key : ∀ h, f h = ∑ q ∈ u, f q * (if h ∈ dcos R K q then 1 else 0) := by
    intro h
    by_cases hex : ∃ q0 ∈ u, h ∈ dcos R K q0
    · obtain ⟨q0, hq0, hh⟩ := hex
      rw [Finset.sum_eq_single q0 (fun q hq hne => ?_) (fun h' => absurd hq0 h'), if_pos hh, mul_one, hinv q0 h hh]
      rw [if_neg, mul_zero]
      intro hq'
      exact hne (hinj hq hq0 ((dcos_eq_of_mem hq').symm.trans (dcos_eq_of_mem hh)))
    · rw [Finset.sum_eq_zero fun q hq => by rw [if_neg fun hh => hex ⟨q, hq, hh⟩, mul_zero]]
      by_contra hne
      obtain ⟨q, hq, r, hr, k, hk, hh⟩ := hsupp h hne
      have hm : dcos R K q ∈ u.image (dcos R K) := himg ▸ Finset.mem_image_of_mem _ hq
      obtain ⟨q', hq', he⟩ := Finset.mem_image.1 hm
      exact hex ⟨q', hq', by rw [he]; exact ⟨r, hr, k, hk, hh⟩⟩
  have hS := quotient_integral_finset_sum u (fun q h => f q * if h ∈ dcos R K q then 1 else 0)
    (fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) * f q) fun q _ => by
      have := (isQuotientIntegral_indicator_doubleCoset R K hR hKc hKo ρ μ q).smul (f q)
      convert this using 1
      · funext h; simp [smul_eq_mul]
      · ring
  convert hS using 1
  exact funext key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProduct
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CommProd

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def mulEquiv (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) : (B × A) ≃ₜ* G where
  toFun p := (p.1 : G) * p.2
  invFun g := ((e.symm g).2, (e.symm g).1)
  left_inv p := by
    have : e.symm ((p.1 : G) * p.2) = (p.2, p.1) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ p.2.2 _ p.1.2]
    simp [this]
  right_inv g := by
    change ((e.symm g).2 : G) * (e.symm g).1 = g
    rw [← hc _ (e.symm g).1.2 _ (e.symm g).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    change ((p.1 * q.1 : B) : G) * ((p.2 * q.2 : A) : G) = ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (p.2 : G), hc _ p.2.2 _ q.1.2]
    simp only [mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (e.symm.continuous.snd).prodMk (e.symm.continuous.fst)

@[simp] theorem mulEquiv_apply (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (p : B × A) : mulEquiv A B hc e he p = (p.1 : G) * p.2 := rfl

def mulEquivSub (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    (R.subgroupOf B × R.subgroupOf A) ≃ₜ* R where
  toFun p := ⟨((p.1 : B) : G) * ((p.2 : A) : G), R.mul_mem (Subgroup.mem_subgroupOf.1 p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)⟩
  invFun r :=
    have h := hR _ (e.symm r).1.2 _ (e.symm r).2.2 (by rw [← he, e.apply_symm_apply]; exact r.2)
    (⟨(e.symm r).2, Subgroup.mem_subgroupOf.2 h.2⟩, ⟨(e.symm r).1, Subgroup.mem_subgroupOf.2 h.1⟩)
  left_inv p := by
    have : e.symm (((p.1 : B) : G) * ((p.2 : A) : G)) = ((p.2 : A), (p.1 : B)) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ (p.2 : A).2 _ (p.1 : B).2]
    ext <;> simp [this]
  right_inv r := by
    apply Subtype.ext
    change ((e.symm r).2 : G) * (e.symm r).1 = r
    rw [← hc _ (e.symm r).1.2 _ (e.symm r).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    apply Subtype.ext
    change (((p.1 * q.1 : R.subgroupOf B) : B) : G) * (((p.2 * q.2 : R.subgroupOf A) : A) : G) =
      (((p.1 : B) : G) * ((p.2 : A) : G)) * (((q.1 : B) : G) * ((q.2 : A) : G))
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc ((p.2 : A) : G), hc _ (p.2 : A).2 _ (q.1 : B).2]
    simp only [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hs : Continuous fun r : R => e.symm r := e.symm.continuous.comp continuous_subtype_val
    exact ((hs.snd).subtype_mk _).prodMk ((hs.fst).subtype_mk _)

@[simp] theorem mulEquivSub_apply (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (p : R.subgroupOf B × R.subgroupOf A) :
    (mulEquivSub A B R hc e he hR p : G) = ((p.1 : B) : G) * ((p.2 : A) : G) := rfl

end GlobalTheory.CommProd

namespace GlobalTheory.CommProd

theorem invInv : ∀ {X Y H : Type} [Group X] [Group Y] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace H] [IsTopologicalGroup X] [IsTopologicalGroup Y] [IsTopologicalGroup H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace H] [BorelSpace X] [BorelSpace Y] [BorelSpace H] [LocallyCompactSpace X]
    [LocallyCompactSpace Y] [LocallyCompactSpace H] [SecondCountableTopology X] [SecondCountableTopology Y]
    [SecondCountableTopology H] (e : (Y × X) ≃ₜ* H) (ρ : Measure Y) (ν : Measure X) (μH : Measure H),
    ρ.IsHaarMeasure → ρ.IsInvInvariant → ν.IsHaarMeasure → μH.IsInvInvariant → (ρ.prod ν).map e = μH →
    ν.IsInvInvariant := by
  intro X Y H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e ρ ν μH _ _ _ _ h
  have he : Measurable e := e.continuous.measurable
  have h1 : (ρ.prod ν.inv).map e = μH := by
    have hp : ρ.prod ν.inv = (ρ.prod ν).map (fun p => p⁻¹) := by
      rw [show (fun p : Y × X => p⁻¹) = Prod.map (·⁻¹) (·⁻¹) from rfl,
        ← Measure.map_prod_map _ _ measurable_inv measurable_inv]
      change ρ.prod ν.inv = ρ.inv.prod ν.inv
      rw [Measure.inv_eq_self ρ]
    have hc : (e ∘ fun p : Y × X => p⁻¹) = (fun q : H => q⁻¹) ∘ e := funext fun p => map_inv e p
    rw [hp, Measure.map_map he measurable_inv, hc, ← Measure.map_map measurable_inv he, h]
    exact Measure.inv_eq_self μH
  have h2 : ρ.prod ν.inv = ρ.prod ν := by
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : (E : Y × X → H) = e := rfl
    rw [← E.map_symm_map (μ := ρ.prod ν.inv), ← E.map_symm_map (μ := ρ.prod ν), hE, h1, h]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : Y)
  have hK0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := ρ) hK1).ne'
  have hKt : ρ K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨Measure.ext fun S hS => ?_⟩
  have := congrArg (fun m : Measure (Y × X) => m (K ×ˢ S)) h2
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hK0 hKt).1 this

theorem cutProd : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G) (he : ∀ p, e p = p.1 * p.2)
    (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (μR : Measure R) (ρ : Measure (R.subgroupOf B))
    (ν : Measure (R.subgroupOf A)) (βB : B → NNReal) (βA : A → NNReal), SFinite ρ → SFinite ν →
    (ρ.prod ν).map (mulEquivSub A B R hc e he hR) = μR →
    GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf B) ρ βB → GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf A) ν βA →
    GlobalTheory.Tw.IsCosetCutoff R μR (fun g => βB (e.symm g).2 * βA (e.symm g).1) := by
  intro G _ _ _ _ _ _ _ _ A B R hc e he hR μR ρ ν βB βA _ _ hm hB hA
  have hs : Measurable fun g : G => e.symm g := e.symm.continuous.measurable
  have hmeas : Measurable fun g : G => βB (e.symm g).2 * βA (e.symm g).1 :=
    (hB.1.comp (measurable_snd.comp hs)).mul (hA.1.comp (measurable_fst.comp hs))
  refine ⟨hmeas, fun x => ?_⟩
  set ψ := mulEquivSub A B R hc e he hR
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hmx : Measurable fun r : R => ((βB (e.symm ((r : G) * x)).2 * βA (e.symm ((r : G) * x)).1 : NNReal) : ℝ≥0∞) :=
    (hmeas.comp (measurable_subtype_coe.mul_const x)).coe_nnreal_ennreal
  rw [← hm, lintegral_map hmx hψ]
  have key : ∀ p : R.subgroupOf B × R.subgroupOf A, e.symm ((ψ p : G) * x) = ((p.2 : A) * (e.symm x).1, (p.1 : B) * (e.symm x).2) := by
    intro p
    rw [Homeomorph.symm_apply_eq, he, mulEquivSub_apply]
    have hx : x = ((e.symm x).1 : G) * (e.symm x).2 := by rw [← he, e.apply_symm_apply]
    have h1 : ((p.1 : B) : G) * ((p.2 : A) : G) = ((p.2 : A) : G) * ((p.1 : B) : G) :=
      (hc _ (p.2 : A).2 _ (p.1 : B).2).symm
    have h2 : ((p.1 : B) : G) * ((e.symm x).1 : G) = ((e.symm x).1 : G) * ((p.1 : B) : G) :=
      (hc _ (e.symm x).1.2 _ (p.1 : B).2).symm
    calc ((p.1 : B) : G) * ((p.2 : A) : G) * x
        = ((p.2 : A) : G) * (((p.1 : B) : G) * ((e.symm x).1 : G)) * (e.symm x).2 := by
          rw [h1]; conv_lhs => rw [hx]
          simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [Subgroup.coe_mul, mul_assoc]
  simp only [key, ENNReal.coe_mul]
  refine (lintegral_prod _ ((hB.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_fst).mul_const _)).mul
    (hA.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_snd).mul_const _))).aemeasurable).trans ?_
  simp only [Pi.mul_apply, Function.comp_apply, lintegral_const_mul' _ _ ENNReal.coe_ne_top, hA.2, mul_one, hB.2]

end GlobalTheory.CommProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CommProd in

theorem GlobalTheory.CommProd.quot_vanish_of_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  intro G _ _ _ _ _ _ _ _ A B R hA hB hR hc ⟨e, he⟩ hdec μR μG ρ μ _ _ _ _ _ _ f z hf hz
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  have : LocallyCompactSpace B := hB.locallyCompactSpace
  have hRA : IsClosed ((R.subgroupOf A : Subgroup A) : Set A) := hR.preimage continuous_subtype_val
  have hRB : IsClosed ((R.subgroupOf B : Subgroup B) : Set B) := hR.preimage continuous_subtype_val
  have : LocallyCompactSpace (R.subgroupOf A) := hRA.locallyCompactSpace
  have : LocallyCompactSpace (R.subgroupOf B) := hRB.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  let φ := mulEquiv A B hc e he
  let ψ := mulEquivSub A B R hc e he hdec
  obtain ⟨μA, hμA, hG⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq φ μ μG
  obtain ⟨ν, hν, hRm⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq ψ ρ μR
  have : ν.IsInvInvariant := invInv ψ ρ ν μR inferInstance inferInstance hν inferInstance hRm
  obtain ⟨βB, -, hβB⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ρ) hRB
  obtain ⟨βA, -, hβA⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ν) hRA
  have hβ := cutProd G A B R hc e he hdec μR ρ ν βB βA inferInstance inferInstance hRm hβB hβA
  obtain ⟨hi, rfl⟩ := hf.cutoff hβ
  have hφs : ∀ p : B × A, e.symm (φ p) = (p.2, p.1) := fun p => by
    rw [Homeomorph.symm_apply_eq, he, mulEquiv_apply, hc _ p.2.2 _ p.1.2]
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hG] at hi ⊢
  rw [hme.integral_map]
  rw [hme.integrable_map_iff] at hi
  refine (integral_prod_symm _ hi).trans ?_
  have hin : ∀ a : A, ∫ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) ∂μ = 0 := by
    intro a
    obtain ⟨-, h0⟩ := (hz a a.2).cutoff hβB
    have e1 : ∀ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) =
        (βA a : ℝ) • ((βB b : ℝ) • f (a * b)) := fun b => by
      simp only [Function.comp_apply, hφs, mulEquiv_apply, NNReal.coe_mul, smul_smul]
      rw [show φ (b, a) = (b : G) * a from rfl, hc _ a.2 _ b.2, mul_comm (βB b : ℝ)]
    simp only [e1, integral_smul, ← h0, smul_zero]
  exact (integral_congr_ae (Filter.Eventually.of_forall hin)).trans (integral_zero _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatMulVecSec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreFrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => q.sec (w i)) =
      fun i => q.sec ((Q.map (GlobalTheory.SliceModel.prH (GlobalTheory.LocMod.ofSplit q)) *ᵥ w) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.SliceModel.ι_mul_left (GlobalTheory.LocMod.ofSplit q) (w j) (incA D (Q i j))

theorem qB_iA_k (p : GlobalTheory.LocMod.Place D k) {ρ : ℕ} (B : BesLev D ρ) :
    B.o.qB.map (GlobalTheory.SliceModel.prH p) * B.o.iA.map (GlobalTheory.SliceModel.prH p) = 0 := by
  rw [← Matrix.map_mul, B.o.qB_iA, Matrix.map_zero _ (map_zero _)]

theorem qB_iB_k (p : GlobalTheory.LocMod.Place D k) {ρ : ℕ} (B : BesLev D ρ) :
    B.o.qB.map (GlobalTheory.SliceModel.prH p) * B.o.iB.map (GlobalTheory.SliceModel.prH p) = 1 := by
  rw [← Matrix.map_mul, B.o.qB_iB, Matrix.map_one _ (map_zero _) (map_one _)]

theorem qB_β {p : GlobalTheory.LocMod.Place D k} {ρ : ℕ} {B : BesLev D ρ} {s : k} {n : Type} [Fintype n] [DecidableEq n]
    {FA : GlobalTheory.LocMod.Frame k B.A.rank n} {C : GlobalTheory.LocMod.Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA C) :
    B.o.qB.map (GlobalTheory.SliceModel.prH p) * C.β =
      fromCols 0 (Matrix.of fun i (_ : Unit) => s * GlobalTheory.SliceModel.prH p (B.ζ i)) := by
  rw [GlobalTheory.SliceModel.β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qB_iA_k, qB_iB_k, Matrix.one_mul,
    Matrix.zero_mul, zero_add]

end GlobalTheory.CoreFrameLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  first | exact @GlobalTheory.CenterScalar.center_scalar | exact GlobalTheory.CenterScalar.center_scalar | (intros; apply GlobalTheory.CenterScalar.center_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallQ
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.VLast

variable {D : D7} {u : D.what₂.Word}

def kerL (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) (φ : GA D (D.sp.X j) → ℂ)
    (h' : GA D D.sp.X') : ℂ :=
  ∫ g in (d.st (j + 1)).fd, (d.pT j h).ω (g, h') ((d.pT j h).pt P₂) 0 *
    (∫ h₀ in (d.x j).vol.𝓕, φ h₀ * (d.p j).ω (embA (d.bes j 0 h).d (d.bes j 0 h).o h₀, g)
      ((d.p j).ω (d.t j, 1) ((d.p j).pt P₁)) 0 ∂(d.x j).vol.μ) ∂(d.st (j + 1)).ν

def smallQ (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (om0 : Om (d.bes j 0 h).V₀ (D.sp.X (j + 1)))
    (omT : Om (D.sp.X (j + 1)) D.sp.X') (φ : GA D (D.sp.X j) → ℂ) (Ξ : WO (d.bes j 0 h).V₀ (D.sp.X (j + 1)) → ℂ)
    (Φ : WO (D.sp.X (j + 1)) D.sp.X' → ℂ) (F : GA D D.sp.X' → ℂ) : ℂ :=
  ∫ h' in d.top.fd, F h' * (∫ g in (d.x (j + 1)).vol.𝓕, omT (g, h') Φ 0 *
    (∫ h₀ in (d.x j).vol.𝓕, φ h₀ * om0 ((d.bes j 0 h).o.emb (h₀, 1), g) Ξ 0 ∂(d.x j).vol.μ) ∂(d.x (j + 1)).vol.μ) ∂d.top.ν

end GlobalTheory.FinPl.VLast

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlaces
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.ParamInert

open Formalism.UG (IsUnramInv GU KU qV IsInertAt)

theorem paramBoundOn_nonsplit (hUDI : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert) :
    ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D A L hL v hv par c hc hc1 w hw
  obtain ⟨⟨C, hC⟩, V, iV, iM, ρ, x, ℓ, hpar, hℓ, hcv⟩ := hc
  have hp := hpar w hw
  refine ⟨hp.card, ?_⟩
  rcases hp with ⟨hs, -⟩ | ⟨hin, τ, ϖ, e, α, hU, he, hsat, hB⟩
  · exact absurd hs hv
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have h4 := hU.2.2.2.1
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  set ϖu : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have hU' : IsUnramInv ((ϖu : w.adicCompletion D.host.E)) τ (qV D.host.F v) := hU
  set ρ' : Representation ℂ (GU τ A.rank) V := ρ.comp e.symm.toMonoidHom with hρ'
  have hKinv : ∀ k ∈ KU τ A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := by
      rw [he.2.2, MulEquiv.apply_symm_apply]; exact hk
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul]
    rw [← map_mul]
    exact hℓ _ hk' _
  have h1 : ℓ x ≠ 0 := by
    intro h0; apply hc1; rw [hcv, map_one]; exact h0
  have hz := (GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal _ ϖu τ (qV D.host.F v) A.rank hU' V ρ' x α hsat ℓ hKinv).2 h1
  have hbd : ∃ C' : ℝ, ∀ g, ‖ℓ (ρ' g x) / ℓ x‖ ≤ C' := by
    refine ⟨C / ‖ℓ x‖, fun g => ?_⟩
    rw [norm_div]
    have : ‖ℓ (ρ' g x)‖ ≤ C := by
      have := hC (e.symm g); rw [hcv] at this; exact this
    exact div_le_div_of_nonneg_right this (norm_nonneg _)
  have htb := GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary hUDI _ ϖu τ (qV D.host.F v) A.rank hU' α _ hz hbd
  intro β hβ
  rw [hB] at hβ
  have hq2 : 2 ≤ qV D.host.F v := hU.2.2.2.2.2.1
  have hle := GlobalTheory.FinZeta.ParamBound.norm_le_of_mem_bcParam hq2 htb β hβ
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 :=
    ((GlobalTheory.LFun.exists_isInertChart _ (isCMExt_host D) v).2 w hw hin).2.2.2.1
  have hqv : (qV D.host.F v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := rfl
  rw [hnorm, Nat.cast_pow, ← hqv]
  refine hle.trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
  · have : (1 : ℝ) ≤ qV D.host.F v := by exact_mod_cast (by omega : 1 ≤ qV D.host.F v)
    nlinarith
  · linarith

end GlobalTheory.Core.Rk.ParamInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_heckeParameters_linearIndependent : ∀ D : D7, ParIndep D := by
  first | exact @GlobalTheory.ChainOnto.parIndep | exact GlobalTheory.ChainOnto.parIndep | (intros; apply GlobalTheory.ChainOnto.parIndep <;> assumption)
end


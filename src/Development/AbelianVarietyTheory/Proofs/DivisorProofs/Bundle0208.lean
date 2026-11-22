import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAlgebraSplittingNormForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
section
open MeasureTheory Filter Topology

namespace GlobalTheory.WeilM.HaarUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] :
    ∃ K : OpenAddSubgroup V, IsCompact (K : Set V) := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  exact ⟨K, hC.of_isClosed_subset K.isClosed hK⟩

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem [IsTopologicalAddGroup V] [T2Space V]
    (K : OpenAddSubgroup V) (hK : IsCompact (K : Set V)) :
    Set.indicator (K : Set V) (fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.WeilM.SB V := by
  simp only [_root_.GlobalTheory.WeilM.SB, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ (K : Set V)
  · exact ⟨K, K.isOpen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set V)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant [NonarchimedeanAddGroup V] {φ : V → ℂ}
    (hφ : φ ∈ _root_.GlobalTheory.WeilM.SB V) :
    ∃ K : OpenAddSubgroup V, ∀ k ∈ K, ∀ x, φ (x + k) = φ x := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨hlc, hcs⟩ := hφ'
  have hnhds : ∀ x : V, (fun w => x + w) ⁻¹' {y | φ y = φ x} ∈ 𝓝 (0 : V) := by
    intro x
    refine (continuous_const_add x).continuousAt.preimage_mem_nhds ?_
    rw [add_zero]
    exact (hlc.isOpen_fiber (φ x)).mem_nhds rfl
  choose W hW using fun x => NonarchimedeanAddGroup.is_nonarchimedean _ (hnhds x)
  have hval : ∀ i y, y - i ∈ W i → φ y = φ i := by
    intro i y hy
    have := hW i hy
    simpa using this
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun i => (fun y => y - i) ⁻¹' (W i))
    (fun i => (W i).isOpen.preimage (continuous_sub_right i))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using (W y).zero_mem⟩)
  refine ⟨t.inf W, fun k hk x => ?_⟩
  have hkW : ∀ i ∈ t, k ∈ W i := fun i hi => (Finset.inf_le hi : t.inf W ≤ W i) hk
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hxi' : x - i ∈ W i := hxi
    have hxk : x + k - i ∈ W i := by
      have := (W i).add_mem hxi' (hkW i hi)
      rwa [sub_add_eq_add_sub] at this
    rw [hval i _ hxk, hval i _ hxi']
  by_cases hxk : x + k ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hxk)
    have hxi' : x + k - i ∈ W i := hxi
    have hx' : x - i ∈ W i := by
      have := (W i).sub_mem hxi' (hkW i hi)
      rwa [sub_right_comm, add_sub_cancel_right] at this
    rw [hval i _ hxi', hval i _ hx']
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxk]

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp [IsTopologicalAddGroup V] (K : OpenAddSubgroup V)
    {φ : V → ℂ} (hc : HasCompactSupport φ) (hinv : ∀ k ∈ K, ∀ x, φ (x + k) = φ x) :
    ∃ S : Finset (V ⧸ K.toAddSubgroup),
      φ = ∑ q ∈ S, φ q.out • (fun x => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (x + -q.out)) := by
  classical
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun p : V => (fun y => -p + y) ⁻¹' (K : Set V))
    (fun p => K.isOpen.preimage (continuous_const_add (-p)))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using K.zero_mem⟩)
  refine ⟨t.image (QuotientAddGroup.mk : V → V ⧸ K.toAddSubgroup), ?_⟩
  funext x
  have hmem : ∀ q : V ⧸ K.toAddSubgroup,
      (x + -q.out ∈ (K : Set V)) ↔ q = (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, add_comm]
    simp
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, hmem,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hS
  · have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup)
    rw [QuotientAddGroup.eq] at h
    have := hinv _ h ((QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup).out)
    rw [add_neg_cancel_left] at this
    exact this
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa using hxp

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
private theorem exists_coeff_form_and_integral [IsTopologicalAddGroup V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ)
    (H : OpenAddSubgroup V) (hH : IsCompact (H : Set V)) {φ : V → ℂ} (hc : HasCompactSupport φ)
    (hinv : ∀ k ∈ H, ∀ x, φ (x + k) = φ x) :
    ∃ A : ℂ, m φ = A * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) ∧
      ∫ x, φ x ∂μ = A * (μ.real (H : Set V) : ℂ) := by
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp H hc hinv
  have hmemH := _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem H hH
  have hint : Integrable (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) μ :=
    (integrable_indicator_iff H.isOpen.measurableSet).2 (integrableOn_const hH.measure_lt_top.ne)
  refine ⟨∑ q ∈ S, φ q.out, ?_, ?_⟩
  · calc m φ = m (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) := congrArg m hS
      _ = ∑ q ∈ S, φ q.out * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, smul_eq_mul, hm _ hmemH]
      _ = _ := by rw [Finset.sum_mul]
  · calc ∫ x, φ x ∂μ = ∫ x, (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) x ∂μ := by
            rw [← hS]
      _ = ∑ q ∈ S, φ q.out * (μ.real (H : Set V) : ℂ) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_finset_sum]
          · refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_const_mul,
              integral_add_right_eq_self (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) x),
              integral_indicator_const _ H.isOpen.measurableSet]
            simp
          · intro q _
            exact (hint.comp_add_right _).const_mul _
      _ = _ := by rw [Finset.sum_mul]

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in

theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral : ∀ (V : Type) [AddCommGroup V]
    [TopologicalSpace V] [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ), (∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ) →
    ∃ c : ℂ, ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, m φ = c * ∫ x, φ x ∂μ := by
  intro V _ _ _ _ _ _ _ μ _ m hm
  obtain ⟨K₀, hK₀⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup (V := V)
  have hpos : ∀ H : OpenAddSubgroup V, IsCompact (H : Set V) → μ.real (H : Set V) ≠ 0 := by
    intro H hH
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨(H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩).ne', hH.measure_lt_top.ne⟩
  refine ⟨m (Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ))) / (μ.real (K₀ : Set V) : ℂ),
    fun φ hφ => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨K₁, hK₁⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant hφ
  set H : OpenAddSubgroup V := K₀ ⊓ K₁
  have hH : IsCompact (H : Set V) := by
    refine hK₀.of_isClosed_subset H.isClosed ?_
    rw [OpenAddSubgroup.coe_inf]
    exact Set.inter_subset_left
  have hHK₁ : ∀ k ∈ H, k ∈ K₁ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.2
  have hHK₀ : ∀ k ∈ H, k ∈ K₀ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.1
  obtain ⟨A, hA₁, hA₂⟩ := exists_coeff_form_and_integral μ m hm H hH hφ'.2
    (fun k hk x => hK₁ k (hHK₁ k hk) x)
  obtain ⟨B, hB₁, hB₂⟩ := exists_coeff_form_and_integral μ m hm H hH
    (φ := Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ)))
    (HasCompactSupport.intro hK₀ fun x hx => Set.indicator_of_notMem hx _)
    (fun k hk x => by
      by_cases hx : x ∈ K₀ <;>
        simp [Set.indicator_apply, hx, add_mem_cancel_right (hHK₀ k hk)])
  rw [integral_indicator_const _ K₀.isOpen.measurableSet, Complex.real_smul, mul_one] at hB₂
  have hH0 : (μ.real (H : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos H hH)
  have hK0 : (μ.real (K₀ : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos K₀ hK₀)
  rw [hA₁, hA₂, hB₁, hB₂]
  have hB0 : B ≠ 0 := by
    rintro rfl
    apply hK0
    rw [hB₂, zero_mul]
  field_simp

end GlobalTheory.WeilM.HaarUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrExtension
section
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum

namespace GlobalTheory.CompleteDVR

theorem exists_place_le {K : Type} [Field K] [NumberField K] (W : ValuationSubring K) :
    ∃ la : HeightOneSpectrum (𝓞 K), (la.valuation K).valuationSubring ≤ W := by
  have hint : ∀ a : 𝓞 K, (a : K) ∈ W := fun a => by
    have h2 : IsIntegral W (a : K) := (RingOfIntegers.isIntegral_coe a).tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2
    rw [← hy]
    exact y.2
  let g : 𝓞 K →+* W := (algebraMap (𝓞 K) K).codRestrict W hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)
  refine ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩,
    fun a ha => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hu : IsUnit (g d) := by
    by_contra hu
    exact d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (𝓞 K) K d * (b : K) = 1 := congrArg Subtype.val hb
  have : a = algebraMap (𝓞 K) K n * (b : K) := by rw [← hnd, mul_assoc, hb', mul_one]
  rw [this]
  exact W.mul_mem _ _ (hint n) b.2

theorem ne_top_of_isDiscreteValuationRing {K : Type} [Field K] (V : ValuationSubring K)
    [IsDiscreteValuationRing V] : V ≠ ⊤ := by
  intro h
  have hall : ∀ y : K, y ∈ V := fun y => h ▸ ValuationSubring.mem_top y
  apply IsDiscreteValuationRing.not_a_field V
  ext x
  simp only [Ideal.mem_bot]
  constructor
  · intro hx
    by_contra hne
    have hne' : (x : K) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    apply (IsLocalRing.mem_maximalIdeal x).1 hx
    refine IsUnit.of_mul_eq_one ⟨(x : K)⁻¹, hall _⟩ (Subtype.ext ?_)
    simp [hne']
  · rintro rfl
    exact Ideal.zero_mem _

theorem exists_complete : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V],
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by
  intro F _ _ V _
  obtain ⟨la, hla⟩ := exists_place_le V
  have hV : (la.valuation F).valuationSubring = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hla (ne_top_of_isDiscreteValuationRing V)
  subst hV
  have hc : IsAdicComplete (maximalIdeal (la.adicCompletionIntegers F)) (la.adicCompletionIntegers F) := by
    refine NormIntegers.isAdicComplete_of_fg (C := la.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : la.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let φ : (la.valuation F).valuationSubring →+* la.adicCompletionIntegers F :=
    ((FinitePlace.embedding la).comp (la.valuation F).valuationSubring.subtype).codRestrict _ (fun x => by
      rw [RingHom.comp_apply, mem_adicCompletionIntegers, ValuationSubring.coe_subtype,
        FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
      exact (Valuation.mem_valuationSubring_iff _ _).1 x.2)
  refine ⟨la.adicCompletionIntegers F, inferInstance, inferInstance, inferInstance, hc, φ, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext ((FinitePlace.embedding la).injective (congrArg Subtype.val h))
  · refine ⟨fun a ha => ?_⟩
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one] at ha
    have h1 : la.valuation F (a : F) = 1 := by
      rw [← valuedAdicCompletion_eq_valuation']
      exact ha
    exact (Valuation.valuationSubring.integers (la.valuation F)).isUnit_iff_valuation_eq_one.2 h1

end GlobalTheory.CompleteDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleZ

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_ccast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃A[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨ContinuousAlgEquiv.refl ℚ _, fun _ => Iff.rfl⟩

theorem exists_clocal (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_ccast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).trans c).trans
    (adicCompletion.padicEquiv w).symm, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

variable (e : ∀ w : HeightOneSpectrum ℤ, (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ)
  (he : ∀ w x, e w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ)

theorem tendsto_primeCorr : Filter.Tendsto primeCorr Filter.cofinite Filter.cofinite :=
  primeCorr.injective.tendsto_cofinite

include he in
theorem maps_int : ∀ᶠ w in Filter.cofinite, Set.MapsTo
    (fun x => ((e w).toRingHom : (primeCorr w).adicCompletion ℚ →+* w.adicCompletion ℚ) x)
      ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) :=
  .of_forall fun w x hx => (he w x).2 hx

def adeleMap : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
      (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ)
      (B₁ := fun v => v.adicCompletionIntegers ℚ) (B₂ := fun w => w.adicCompletionIntegers ℚ)
      primeCorr tendsto_primeCorr (fun w => (e w).toRingHom) (maps_int e he)

theorem continuous_adeleMap : Continuous (adeleMap e he) :=
  RestrictedProduct.mapAlong_continuous _ _ primeCorr tendsto_primeCorr _ (maps_int e he)
    fun w => (e w).continuous

def adeleAlgHom : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] FiniteAdeleRing ℤ ℚ where
  toFun a := ⟨fun w => e w (a (primeCorr w)), by
    have h1 := primeCorr.injective.tendsto_cofinite.eventually a.2
    exact h1.mono fun w hw => (he w _).2 hw⟩
  map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
  map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
  map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
  map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
  commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r

theorem adeleAlgHom_apply (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (w : HeightOneSpectrum ℤ) :
    adeleAlgHom e he a w = e w (a (primeCorr w)) := rfl

theorem adeleAlgHom_eq : ⇑(adeleAlgHom e he) = ⇑(adeleMap e he) := by
  funext a
  exact FiniteAdeleRing.ext _ fun w => rfl

theorem adeleAlgHom_injective : Function.Injective (adeleAlgHom e he) := by
  intro a b hab
  refine FiniteAdeleRing.ext _ fun v => ?_
  obtain ⟨w, rfl⟩ := primeCorr.surjective v
  have h := congrArg (fun x : FiniteAdeleRing ℤ ℚ => x w) hab
  simp only [adeleAlgHom_apply] at h
  exact (e w).injective h

theorem adeleAlgHom_surjective : Function.Surjective (adeleAlgHom e he) := by
  intro b
  obtain ⟨f, hf⟩ : ∃ f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ,
      ∀ w, f (primeCorr w) = (e w).symm (b w) :=
    ⟨_, fun w => Equiv.piCongrLeft_apply_apply
      (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ) primeCorr
      (fun w => (e w).symm (b w)) w⟩
  have hfi : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ := by
    have h1 := primeCorr.symm.injective.tendsto_cofinite.eventually b.2
    refine h1.mono fun v hv => ?_
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    rw [Equiv.symm_apply_apply] at hv
    rw [hf, ← he, ContinuousAlgEquiv.apply_symm_apply]
    exact hv
  obtain ⟨a, ha⟩ : ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ, ∀ v, a v = f v := ⟨⟨f, hfi⟩, fun _ => rfl⟩
  refine ⟨a, FiniteAdeleRing.ext _ fun w => ?_⟩
  rw [adeleAlgHom_apply, ha, hf, ContinuousAlgEquiv.apply_symm_apply]

omit e he in

theorem exists_continuous_adele_equiv :
    ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  choose e he using exists_clocal
  refine ⟨AlgEquiv.ofBijective (adeleAlgHom e he)
    ⟨adeleAlgHom_injective e he, adeleAlgHom_surjective e he⟩, ?_⟩
  change Continuous (adeleAlgHom e he)
  rw [adeleAlgHom_eq]
  exact continuous_adeleMap e he

end GlobalTheory.AdeleZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivFourierClassesPosConeSummand
section
open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Div.QFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem (𝔞 : Frac F) (ε : (𝓞 F)ˣ) {x : F} (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ((ε : 𝓞 F) : F) * x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hx
  rw [Algebra.smul_def] at this
  exact this

def toQ (𝔞 𝔟 : Frac F) (x : Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) : Quotient (qRel 𝔞 𝔟) :=
  Quotient.mk _ ⟨(x.2.1, rep x.1), x.2.2.1, rep_mem x.1, x.2.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨β, ν, hν⟩ ⟨β', ν', hν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  simp only at h1 h2
  have hβ : β = β' := by
    rw [← Quotient.out_eq β, ← Quotient.out_eq β']
    exact Quotient.sound ⟨ε, h2⟩
  subst hβ
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h0 := rep_ne_zero β
    have : (((ε : 𝓞 F) : F) - 1) * rep β = 0 := by unfold rep at h2 ⊢; rw [sub_mul, ← h2]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : (⟨ν, hν⟩ : posCone 𝔞 (rep β)) = ⟨ν', hν'⟩ := Subtype.ext h1.symm
  rw [this]

theorem exists_emb [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨(IsTotallyReal.complexEmbedding_isReal w.embedding).embedding⟩

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro c
  induction c using Quotient.ind with
  | _ p =>
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨τ⟩ := exists_emb (F := F)
    have := hpos τ; simp at this
  let β : NzCls 𝔟 := Quotient.mk _ ⟨b, hb, hb0⟩
  obtain ⟨ε, hε⟩ : (unitRel 𝔟).r (Quotient.out β) ⟨b, hb, hb0⟩ := Quotient.exact (Quotient.out_eq β)
  have h4 := unit_inv_mul ε
  have hrep : rep β = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * b := by
    unfold rep; simp only at hε; rw [hε, ← mul_assoc, h4, one_mul]
  have hprod : ((ε : 𝓞 F) : F) * ν * rep β = ν * b := by
    rw [hrep]; linear_combination (ν * b) * h4
  refine ⟨⟨β, ((ε : 𝓞 F) : F) * ν, unit_mul_mem 𝔞 ε hν, fun τ => by rw [hprod]; exact hpos τ⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, ?_⟩
  · show ν = _ * (((ε : 𝓞 F) : F) * ν)
    rw [← mul_assoc, h4, one_mul]
  · show b = ((ε : 𝓞 F) : F) * rep β
    rw [hrep, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), h4, one_mul]

theorem qFibres : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)) ≃ Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟),
      ∀ (k : ℕ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (e x) = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (x.2.1, GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩, fun k z x => ?_⟩
  exact qClass_mk 𝔞 𝔟 k z _

end GlobalTheory.Div.QFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAlgebraSplittingNormFormStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_algebra_splitting_normForm : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R), Function.Injective (algebraMap A R) ∧ Module.Finite A R ∧
      ∃ σ : Fin (Module.finrank K L) → (B →+* R), (∀ j, (σ j).comp φ = algebraMap A R) ∧
        ∀ (m : ℕ) (g : Fin m → B), ∃ P : MvPolynomial (Fin m) A,
          P.map (algebraMap A K) = GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i)) ∧
          P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i := by
  first | exact @GlobalTheory.NormSheaf.exists_finite_split_normForm | exact GlobalTheory.NormSheaf.exists_finite_split_normForm | (intros; apply GlobalTheory.NormSheaf.exists_finite_split_normForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)), ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  first | (exact @GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (exact GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (intros; apply GlobalTheory.EtC.exists_finset_mem_firstAndFinite  <;> assumption)
end


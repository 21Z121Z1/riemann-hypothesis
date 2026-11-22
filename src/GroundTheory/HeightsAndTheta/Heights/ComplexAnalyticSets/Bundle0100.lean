import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0001
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0015
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0090

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightOneGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem isCohenMacaulayLocalRing_of_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hgW : g ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W := by rwa [Ideal.mk_ker]
  set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'
  have : W'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : W'.comap (Ideal.Quotient.mk J) = W := by
    rw [hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W := fun a => by
    rw [← Ideal.mem_comap, hcomap]
  have hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      obtain ⟨b, hb, hba⟩ := Submonoid.mem_map.mp hx
      change Ideal.Quotient.mk J a ∉ W'
      rw [← hba, hmem]
      exact hb
    · intro ha
      exact Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      W' := by
    have h := Vertical.SpecChart.isLocalization_quot W J
    rw [hsub] at h
    exact h
  have : IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.AtPrime.isLocalRing _ W'
  have : IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors W')
  set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
    (Ideal.Quotient.mk J g) with hx
  have hg0 : Ideal.Quotient.mk J g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx0 : x ≠ 0 := by
    intro h
    apply hg0
    have h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0 := by
      rw [map_zero]
      exact h
    exact IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0
  have hxm : x ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W']
    exact Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)
  have hheight : W'.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    apply hg0
    rw [← Ideal.mem_bot, ← h]
    exact (hmem g).mpr hgW
  refine { exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hxm
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b hab
    simp only [smul_eq_mul] at hab
    exact mul_left_cancel₀ hx0 hab
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]
    simp

theorem CMHeightOneGeneral.proof (hopen : CMLocusOpen.Statement) : CMHeightOneGeneral.Statement := by
  intro n J W g hJ hg hW
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  obtain ⟨f, hfW, hf⟩ := hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := fun p hp =>
    RingHom.mem_ker.mpr (hq p hp)
  exact hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMProjDimCriterion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

theorem exists_nat_eq_of_ne_bot_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe y =>
    have hy : y ≤ (d : ℕ∞) := by exact_mod_cast hle
    have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy
    exact ⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩

theorem quotient_mk_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]
  have h2 : (1 : S) ∈ maximalIdeal S := by
    have := sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

theorem mem_maximalIdeal_of_quotient_mk {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] {r : S} (hr : Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J)) : r ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  exact fun hu => hr (hu.map _)

theorem isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨rs0, hrs0, hofl, hlen0⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)
  have hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S := fun r hr => hofl ▸ Ideal.subset_span hr
  set d := rs0.length with hd_def
  have hcmS : IsCohenMacaulayLocalRing S :=
    { exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }
  have hsum := hcm S J hJ
  rw [← hlen0] at hsum
  obtain ⟨e, he⟩ := exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d)
    (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)
  have hht : J.height ≠ ⊤ := by
    intro h
    rw [h, he] at hsum
    have h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d := by exact_mod_cast hsum
    simp at h2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, J.height = h := ⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩
  have hhe : h + e = d := by
    rw [hh, he] at hsum; exact_mod_cast hsum
  have hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d :=
    GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)
  constructor
  · intro hCM
    obtain ⟨as, has_m, has_reg, has_len⟩ := hCM.exists_isWeaklyRegular
    obtain ⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as :=
      ⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by
        rw [List.map_map]; conv_rhs => rw [← List.map_id as]
        exact List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩
    have hmsreg : IsWeaklyRegular (S ⧸ J) ms := by
      rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]; exact has_reg
    have hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S := fun r hr =>
      mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))
    have hmslen : ms.length = e := by
      have : (as.length : WithBot ℕ∞) = e := has_len.symm.trans he
      rw [← hms, List.length_map] at this; exact_mod_cast this
    have hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d :=
      fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this
    refine ⟨d - e, ?_, ?_⟩
    · have := hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg
      rwa [hmslen] at this
    · rw [hh]; exact_mod_cast (by omega : d - e ≤ h)
  · rintro ⟨ℓ, hpd, hℓ⟩
    obtain ⟨ms, hmsm, hmsreg, hmslen⟩ := hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular
    have hℓh : ℓ ≤ h := by rw [hh] at hℓ; exact_mod_cast hℓ
    have hle : e ≤ ms.length := by rw [hmslen]; omega
    have hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e) := by
      have := hmsreg; rw [← List.take_append_drop e ms] at this
      exact ((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1
    refine { exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))
    · exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'
    · rw [he, List.length_map, List.length_take, min_eq_left hle]

theorem CMProjDimCriterion.proof (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by
  intro n I Q _ hIQ
  have : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q
  refine isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hIQ

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartIntCountAdd

variable {n d : ℕ}

theorem hasSum_indicator {E : ℕ → Set (Fin n → ℂ)} (hE : Pairwise (Function.onFun Disjoint E))
    (g : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    HasSum (fun i => (E i).indicator g x) ((⋃ i, E i).indicator g x) := by
  by_cases hx : x ∈ ⋃ i, E i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hval : (⋃ i, E i).indicator g x = (E j).indicator g x := by
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hj]
    rw [hval]
    refine hasSum_single j fun i hi => ?_
    have hxi : x ∉ E i := fun hxi => Set.disjoint_left.1 (hE hi) hxi hj
    simp [hxi]
  · have h0 : ∀ i, (E i).indicator g x = 0 := fun i => by
      have hxi : x ∉ E i := fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)
      simp [hxi]
    have hu : (⋃ i, E i).indicator g x = 0 := by simp only [Set.indicator_of_notMem hx]
    simp only [h0, hu]
    exact hasSum_zero

open Classical in

theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, (if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0) := by
  unfold sheetSum
  exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hasSum_sheetSum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : ℕ → (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (hF : ∀ x s, HasSum (fun i => F i x s) (G x s)) :
    HasSum (fun i => sheetSum J A (F i) y) (sheetSum J A G y) := by
  classical
  simp only [sheetSum_eq_sum hfin]
  refine hasSum_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hF x _
  · simp only [dif_neg h]; exact hasSum_zero

theorem abs_sheetSum_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    |sheetSum J A F y| ≤ sheetSum J A (fun x s => |F x s|) y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h, abs_zero, le_refl]

theorem sheetSum_mono {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ}
    (hFG : ∀ x s, F x s ≤ G x s) : sheetSum J A F y ≤ sheetSum J A G y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hFG x _
  · simp only [dif_neg h, le_refl]

theorem indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    S.indicator f x * c = S.indicator (fun z => f z * c) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| = S.indicator (fun z => |f z * c|) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul_le (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| ≤ |f x * c| := by
  by_cases hx : x ∈ S <;> simp [hx] <;> positivity

end ChartIntCountAdd

open ChartIntCountAdd in

theorem ChartIntCountAdd.proof (hCM : ChartMassCompact.Statement) : ChartIntCountAdd.Statement := by
  intro n d W A f φ E hW hdim hA hf hfc hφ hEm hE
  have hfin : ∀ y, (fibre W A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
  have hmeas : ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
      Measurable (chartDens W A g φ) ∧ Measurable (chartAbsDens W A g φ) := fun g hg =>
    SheetSumMeasurable.proof n d W A g φ hW hdim hA hg hφ
  have hgm : ∀ i, Measurable ((E i).indicator f) := fun i => hf.measurable.indicator (hEm i)
  have hgu : Measurable ((⋃ i, E i).indicator f) := hf.measurable.indicator (MeasurableSet.iUnion hEm)

  have hdens : ∀ y, HasSum (fun i => chartDens W A ((E i).indicator f) φ y)
      (chartDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [indicator_mul]
    exact hasSum_indicator hE _ x
  have habs : ∀ y, HasSum (fun i => chartAbsDens W A ((E i).indicator f) φ y)
      (chartAbsDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartAbsDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [abs_indicator_mul]
    exact hasSum_indicator hE _ x

  have hdom : Integrable (chartAbsDens W A ((⋃ i, E i).indicator f) φ) := by
    refine (hCM n d W A f φ hW hdim hA hf.continuousOn hφ (Or.inl hfc)).mono'
      (hmeas _ hgu).2.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartAbsDens
    refine (abs_sheetSum_le (hfin y) _).trans (sheetSum_mono (hfin y) fun x s => ?_)
    rw [abs_abs]
    exact abs_indicator_mul_le _ _ _ _
  have hsum : (fun y => ∑' i, chartAbsDens W A ((E i).indicator f) φ y) =
      chartAbsDens W A ((⋃ i, E i).indicator f) φ := funext fun y => (habs y).tsum_eq
  exact hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun i => chartDens W A ((E i).indicator f) φ)
    (f := chartDens W A ((⋃ i, E i).indicator f) φ)
    (fun i => chartAbsDens W A ((E i).indicator f) φ)
    (fun i => (hmeas _ (hgm i)).1.aestronglyMeasurable)
    (fun i => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact abs_sheetSum_le (hfin y) _)
    (ae_of_all _ fun y => (habs y).summable)
    (by rw [hsum]; exact hdom)
    (ae_of_all _ hdens)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal

noncomputable section

namespace ChartMassCompact

variable {n d : ℕ}

theorem mdisc_coord_zero {D : ℕ} (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (hi : M i = 0) : ReciprocityTheory.AnForm.mdisc M = 0 := by
  rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨j, hj⟩ := hr i
    refine mul_eq_zero_of_right _ (Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_)
    simp [hj, hi]
  · rw [ReciprocityTheory.AnForm.A.polCoef_eq_zero r hr, zero_mul]

theorem hessC_eq_zero_of_eventuallyEq {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] 0) : ReciprocityTheory.AnForm.hessC φ z = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ (0 : (Fin D → ℂ) → ℝ) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ φ) z = 0 := by
    rw [h1.fderiv_eq]
    simp
  ext i j
  simp [ReciprocityTheory.AnForm.hessC, h2]

theorem maDens_eq_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (i : Fin d) (hx : x ∉ tsupport (ψ i)) :
    ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
  obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := (hsd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hev : (ψ i ∘ s) =ᶠ[𝓝 (A *ᵥ x)] 0 := by
    have hnhds : (tsupport (ψ i))ᶜ ∈ 𝓝 (s (A *ᵥ x)) := by
      rw [hsx]
      exact (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    filter_upwards [hcont.preimage_mem_nhds hnhds] with y hy
    show ψ i (s y) = 0
    exact image_eq_zero_of_notMem_tsupport hy
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_coord_zero _ i (hessC_eq_zero_of_eventuallyEq hev)]
  simp

theorem integrable_ball (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (ψ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (hψ : ∀ k, SmoothNear (zeroSet J) (ψ k)) (R : ℝ) :
    Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ) := by
  obtain ⟨K, hK, hle⟩ := hC n d J A ψ R hJ hd hA hψ
  have hmeas := (SheetSumMeasurable.proof n d J A
    ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ hJ hd hA
    (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbd : Bornology.IsBounded
      (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
    (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
  obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
  have h1 := hle (fun _ => 1) measurable_const
  simp only [enorm_one, setLIntegral_one] at h1
  refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
  exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hMF n d J hJ hd R')

theorem chartAbsDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {K B : Set (Fin n → ℂ)} {M : ℝ}
    (hKB : K ⊆ B) (hM : ∀ x ∈ zeroSet J ∩ K, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hvan : ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0)
    (y : Fin d → ℂ) (hfin : (fibre J A y).Finite) :
    chartAbsDens J A f ψ y ≤ M * chartAbsDens J A (B.indicator fun _ => 1) ψ y := by
  classical
  unfold chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  split_ifs with h
  · dsimp only
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem (hKB hxK), one_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM x ⟨hxZ, hxK⟩) (abs_nonneg _)
    · rw [hvan x _ h.choose_spec hxK, abs_zero]
      positivity
  · simp

end ChartMassCompact

open ChartMassCompact in

theorem ChartMassCompact.proof (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement) :
    ChartMassCompact.Statement := by
  classical
  intro n d J A f ψ hJ hd hA hf hψ hsupp
  obtain ⟨K, hKc, hvan⟩ : ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
    rcases hsupp with hc | ⟨i, hc⟩
    · exact ⟨tsupport f, hc, fun x s _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩
    · exact ⟨tsupport (ψ i), hc, fun x s hs hx => by rw [maDens_eq_zero hs ψ i hx, mul_zero]⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKc.isBounded
  obtain ⟨M, hM⟩ := (hKc.inter_left (SheetSumMeasurable.isClosed_zeroSet J)).exists_bound_of_continuousOn
    (hf.mono Set.inter_subset_left)
  have heq : chartAbsDens J A f ψ = chartAbsDens J A ((zeroSet J).piecewise f 0) ψ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hgm : Measurable ((zeroSet J).piecewise f 0) :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : AEStronglyMeasurable (chartAbsDens J A f ψ) volume := by
    rw [heq]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hd hA hgm hψ).2.aestronglyMeasurable
  refine ((integrable_ball hC hMF J A ψ hJ hd hA hψ R).const_mul (max M 0)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  exact chartAbsDens_le J A f ψ hR (fun x hx => (Real.norm_eq_abs (f x) ▸ hM x hx).trans (le_max_left _ _))
    (le_max_right _ _) hvan y (FibreBound.proof n d J A hJ hd hA y).2.1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormEnergyDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LogNormEnergyDensNonneg.proof : LogNormEnergyDensNonneg.Statement := by
  intro n d h s y v hs hsy
  exact LogNormGradDensNonneg.proof n d h s y v hs hsy

end GroundTheory.Heights₂.Heights
end


import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOrderLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem subring_map_maximal_cases {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by
  by_cases h : m ≤ (IsLocalRing.maximalIdeal D).comap C.subtype
  · right
    rw [hm.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal D).ne_top) h]
    exact hC
  · left
    obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp h
    have hu : IsUnit (C.subtype c) := by
      by_contra hnu
      exact hc (IsLocalRing.mem_maximalIdeal _ |>.mpr hnu)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hcm) hu

theorem length_quot_le_of_subring (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  let _ : Algebra A C := f.toAlgebra
  have s3 := h₃ A C hdim hfinj
    (fun c => by
      obtain ⟨b, hb, hbc⟩ := hfrac c
      exact ⟨b, hb, by rw [Algebra.smul_def]; exact hbc⟩) a ha
  have s2 : Module.length C (C ⧸ Ideal.span {algebraMap A C a}) ≤
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) := by
    have h := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at h
  have s1 := h₂ C D C.subtype (subring_map_maximal_cases C hmax) (Ideal.span {algebraMap A C a})
  rw [Ideal.map_span, Set.image_singleton] at s1
  exact s1.trans (s2.trans s3)

theorem BlowUpOrderLe.proof (h₁ : LocalizedQuotLength.Statement.{u})
    (h₂ : LengthMapIdealLe.Statement.{u}) (h₃ : IntermediateRingQuotLength.Statement.{u})
    (h₄ : BlowUpLocalChart.Statement.{u}) : BlowUpOrderLe.Statement.{u} := by
  intro R _ _ K _ ι _ J _ P hP u G' y hy hG' hrel x hx hG z hz
  have hGp : G'.IsPrime := hG'.1.1
  obtain ⟨G₀, W₀, hG₀p, hW₀p, hG₀, hW₀⟩ := BlowUpLocalChart.exists_quotient_primes hGp
    (le_sup_left.trans hG'.1.2) (le_sup_left.trans hG.1.2)
  have hRHS0 : (0 : ℤ) ≤ divCycle P z (G'.comap (liftForm (J := J))) := by
    unfold divCycle
    split_ifs <;> positivity
  by_cases hL : G' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm z}).minimalPrimes ∧ IsRelevant G'
  swap
  · have h0 : divCycle (blowUpOf P u) (liftForm z) G' = 0 := by
      unfold divCycle
      rw [dif_neg hL]
    rw [h0]
    exact hRHS0
  have hzG : z ∈ G'.comap (liftForm (J := J)) :=
    hL.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcp : (G'.comap (liftForm (J := J))).IsPrime := hG.1.1
  have hRmin : G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {z}).minimalPrimes := by
    have h := mem_minimalPrimes_sup_span_mul (P := P) (W := G'.comap (liftForm (J := J))) hz hG
    refine ⟨⟨hcp, sup_le (le_sup_left.trans hG.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hzG)⟩, ?_⟩
    intro q hq hqG
    refine h.2 ⟨hq.1, sup_le (le_sup_left.trans hq.2) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hqG
    exact q.mul_mem_left x (hq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z)))
  have hRrel : IsRelevant (G'.comap (liftForm (J := J))) := by
    intro k
    obtain ⟨i, hi⟩ := hL.2 (some k)
    refine ⟨i, fun hmem => hi ?_⟩
    rw [Ideal.mem_comap] at hmem
    simpa [liftForm, rename_X] using hmem
  have hfin := length_localizedQuot_ne_top (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) hRmin
  unfold divCycle
  rw [dif_pos hL, dif_pos ⟨hRmin, hRrel⟩]
  suffices key : multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) G' ≤
      multAt (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) by
    exact_mod_cast ENat.toNat_le_toNat key hfin

  obtain ⟨C, f, hfinj, hfrac, hfcompat, hmax⟩ := h₄ R K ι J P hP u G' y hy hG' hrel x hx hG G₀ hG₀ W₀ hW₀
  have hQp : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hSn : IsNoetherianRing (MRing ι R ⧸ P) := inferInstance
  have hAn : IsNoetherianRing (Localization.AtPrime G₀) :=
    IsLocalization.isNoetherianRing G₀.primeCompl _ hSn
  have hAinj : Function.Injective (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀)) :=
    IsLocalization.injective (Localization.AtPrime G₀) (Ideal.primeCompl_le_nonZeroDivisors G₀)
  have hdim : ringKrullDim (Localization.AtPrime G₀) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height G₀ (Localization.AtPrime G₀)]
    have hmap : (G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P) = G₀ := by
      rw [← hG₀, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hle : G₀.height ≤ 1 := hmap ▸ Ideal.map_height_le_one_of_mem_minimalPrimes hG
    have hne : G₀.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      have hxG : Ideal.Quotient.mk P x ∈ G₀ := by
        rw [← Ideal.mem_comap, hG₀]
        exact hG.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hxG
      exact hx hxG
    have h1 : G₀.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
    rw [h1]
    rfl
  set a : Localization.AtPrime G₀ :=
    algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P z) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    rw [ha_def, ← map_zero (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀))] at h0
    exact hz (Ideal.Quotient.eq_zero_iff_mem.mp (hAinj h0))
  have hDom : IsDomain (Localization.AtPrime W₀) := inferInstance
  have hchain := length_quot_le_of_subring h₂ h₃ hdim C f hfinj hfrac hmax a ha
  rw [ha_def, hfcompat z] at hchain
  have e₁ := h₁ (MRing (extIdx ι J) R) (blowUpOf P u) W₀ (liftForm z)
  have e₂ := h₁ (MRing ι R) P G₀ z
  have key : ∀ (H : Ideal (MRing (extIdx ι J) R)) [H.IsPrime] (G : Ideal (MRing ι R)) [G.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = H → G₀.comap (Ideal.Quotient.mk P) = G →
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) H ≤ multAt (P ⊔ Ideal.span {z}) G := by
    intro H _ G _ hH hGG
    subst hH
    subst hGG
    unfold multAt
    exact e₁.le.trans (hchain.trans e₂.ge)
  exact key _ _ hW₀ hG₀

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimTwoSumReading
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing

noncomputable section

namespace DimTwoSumReading

variable {A : Type*} [CommRing A]

theorem length_loc_eq_ordLoc (W : Ideal A) [hW : W.IsPrime] (a : A) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc ⟨W, hW⟩ a := by
  have h := length_localizedModule_quot_eq (T := Localization.AtPrime W) W.primeCompl ⊥ a
    (fun s hs => IsLocalization.map_units _ (⟨s, hs⟩ : W.primeCompl))
    (fun y => by
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj W.primeCompl y
      exact ⟨r, s, s.2, hy.symm⟩)
    (fun r hr => by
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff W.primeCompl _ r).mp hr
      exact ⟨s, s.2, (Ideal.mem_bot).mpr hs⟩)
    (fun v hv => by rw [(Ideal.mem_bot).mp hv, map_zero])
  rw [bot_sup_eq] at h
  exact h

theorem length_max_eq_ordMod [IsLocalRing A] (W : Ideal A) [hW : W.IsPrime] (b : A) :
    Module.length (Localization.AtPrime (maximalIdeal A))
        (LocalizedModule (maximalIdeal A).primeCompl (A ⧸ (W ⊔ Ideal.span {b}))) =
      ordMod ⟨W, hW⟩ b := by
  have h := length_localizedModule_quot_eq (T := A ⧸ W) (maximalIdeal A).primeCompl W b
    (fun s hs => (notMem_maximalIdeal.mp hs).map _)
    (fun y => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨r, 1, (maximalIdeal A).primeCompl.one_mem, by simp⟩)
    (fun r hr => ⟨1, (maximalIdeal A).primeCompl.one_mem, by
      rw [one_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mp hr⟩)
    (fun v hv => Ideal.Quotient.eq_zero_iff_mem.mpr hv)
  rw [h, ordMod, Ring.ord, Ideal.Quotient.algebraMap_eq]

variable [IsDomain A] [IsNoetherianRing A]

theorem mem_minimalPrimes_iff {a : A} (ha : a ≠ 0) (W : Ideal A) [W.IsPrime] :
    W ∈ (Ideal.span {a}).minimalPrimes ↔ W.height = 1 ∧ a ∈ W := by
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  constructor
  · intro hW
    have haW : a ∈ W := hW.1.2 (Ideal.subset_span rfl)
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) W hW
    have h0 : W.height ≠ 0 := fun h => ha ((Ideal.mem_bot).mp (Ideal.height_eq_zero_iff_eq_bot.mp h ▸ haW))
    exact ⟨le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), haW⟩
  · rintro ⟨h1, haW⟩
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := W)
      ((Ideal.span_singleton_le_iff_mem W).mpr haW)
    rcases hQW.lt_or_eq with hlt | rfl
    · have := hQ.1.1
      have haQ : a ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
      have hbQ : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun h => ha ((Ideal.mem_bot).mp (h ▸ haQ))
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbQ
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at e1
      rw [h1] at e2
      have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add e1 le_rfl) e2
      exact absurd this (by decide)
    · exact hQ

omit [IsDomain A] [IsNoetherianRing A] in

theorem max_mem_minimalPrimes [IsLocalRing A] (h2 : ringKrullDim A = 2) (W : Ideal A) [hW : W.IsPrime]
    (h1 : W.height = 1) {b : A} (hbW : b ∉ W) (hbm : b ∈ maximalIdeal A) :
    maximalIdeal A ∈ (W ⊔ Ideal.span {b}).minimalPrimes := by
  have hle : W ⊔ Ideal.span {b} ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hW.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  refine ⟨⟨(maximalIdeal.isMaximal A).isPrime, hle⟩, fun Q hQ hQm => ?_⟩
  have := hQ.1
  by_contra hne
  have hlt : Q < maximalIdeal A := lt_of_le_of_ne hQm fun h => hne (h ▸ le_rfl)
  have hWQ : W < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
    hbW (h ▸ hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hWQ
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [h2, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hm
  rw [WithBot.coe_injective hm] at e2
  rw [h1] at e1
  have : (1 : ℕ∞) + 1 + 1 ≤ 2 := le_trans (add_le_add e1 le_rfl) e2
  exact absurd this (by decide)

end DimTwoSumReading

open DimTwoSumReading in

theorem DimTwoSumReading.proof : DimTwoSumReading.Statement := by
  intro A _ _ _ _ h2 a b ha hab
  classical
  have hT : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)).subset
      (fun p hp => (mem_minimalPrimes_iff ha p.asIdeal).mpr hp)
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal →
      (locCycle (Ideal.span {a}) p.asIdeal = ((ordLoc p a).toNat : ℤ) ∧ ordLoc p a ≠ ⊤) ∧
      (locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = ((ordMod p b).toNat : ℤ) ∧
        ordMod p b ≠ ⊤) := by
    intro p hp
    have hmin := (mem_minimalPrimes_iff ha p.asIdeal).mpr hp
    have hlA := length_loc_eq_ordLoc p.asIdeal a
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold locCycle; rw [dif_pos hmin]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlA
    · rw [← hlA]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmin
    by_cases hbm : b ∈ maximalIdeal A
    · have hmm := max_mem_minimalPrimes h2 p.asIdeal hp.1 (hab _ p.isPrime hp.1 hp.2) hbm
      have hlB := length_max_eq_ordMod p.asIdeal b
      refine ⟨?_, ?_⟩
      · unfold locCycle; rw [dif_pos hmm]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlB
      · rw [← hlB]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmm
    · have h0 : ordMod p b = 0 := Ring.ord_of_isUnit ((notMem_maximalIdeal.mp hbm).map _)
      have hnm : maximalIdeal A ∉ (p.asIdeal ⊔ Ideal.span {b}).minimalPrimes := fun h =>
        hbm (h.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      rw [h0]
      refine ⟨?_, ENat.zero_ne_top⟩
      unfold locCycle; rw [dif_neg hnm]; rfl
  have hsupp : Function.support (fun W : Ideal A => locCycle (Ideal.span {a}) W *
      locCycle (W ⊔ Ideal.span {b}) (maximalIdeal A)) ⊆
      (hT.toFinset.map ⟨PrimeSpectrum.asIdeal, by intro p q h; exact PrimeSpectrum.ext h⟩ : Finset (Ideal A)) := by
    intro W hW
    have hne : locCycle (Ideal.span {a}) W ≠ 0 := left_ne_zero_of_mul hW
    have hmin : W ∈ (Ideal.span {a}).minimalPrimes := by
      by_contra h
      exact hne (by unfold locCycle; rw [dif_neg h])
    have := hmin.1.1
    rw [Finset.coe_map, Set.Finite.coe_toFinset]
    exact ⟨⟨W, hmin.1.1⟩, (mem_minimalPrimes_iff ha W).mp hmin, rfl⟩
  refine ⟨∑ p ∈ hT.toFinset, (ordLoc p a).toNat * (ordMod p b).toNat, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    show locCycle (Ideal.span {a}) p.asIdeal * locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = _
    rw [hk.1.1, hk.2.1]
  · refine (finsum_mem_eq_finite_toFinset_sum (fun p => ordLoc p a * ordMod p b) hT).trans ?_
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    rw [ENat.natCast_toNat hk.1.2, ENat.natCast_toNat hk.2.2]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F] {M : ℕ}

theorem chartMon_not_mem {W : Ideal (MRing (bundleIdx ι M) F)} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W) (α : K → ℕ) :
    chartMon F M c α ∉ W := by
  unfold chartMon
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, _, hk⟩
  exact hc k (hW.mem_of_pow_mem _ hk)

end FlagLineSectionProof

open FlagLineSectionProof in

theorem FlagLineSection.proof : FlagLineSection.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy _ N E _ _ B w b hB M a φ hφ Φ _ _ t ht h0
  have hXn : ∀ l : Fin M, projMap F y w φ (truncCoord t 1) (X ⟨none, l⟩) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l (w ⟨0, h0⟩))) * X none := by
    intro l
    rw [projMap_X_none, sum_truncCoord_one t h0]
  have ht0 : t ⟨0, h0⟩ ≠ 0 := fun h => ht.transcendental ⟨0, h0⟩ (h ▸ isAlgebraic_zero)

  have hyne : ∀ k (i : ι k), (X ⟨k, i⟩ : MRing ι F) ∉ pointIdeal F y → y ⟨k, i⟩ ≠ 0 := by
    intro k i hX h
    apply hX
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h]
  choose c0 hc0 using hy.relevant
  have live0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => hyne k _ (hc0 k)
  have hs0 := segreVec_ne_zero_of_live live0
  obtain ⟨hξ0, v0, -, hsum0⟩ := chart_data y B w b hB a φ hφ c0 hs0 h0
  obtain ⟨l0, hl0⟩ : ∃ l0, φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hsum0
  have hu0 : φ l0 (w ⟨0, h0⟩) ≠ 0 := left_ne_zero_of_mul hl0
  obtain ⟨n0, A0, hA0⟩ := exists_chartForm (M := M) y w φ (truncCoord t 1) c0 hs0 (hξ0 l0)
  obtain ⟨p, q, hpq⟩ : ∃ p q : K → ℕ, ∀ k, (p k : ℤ) - q k = -(b ⟨0, h0⟩ k - a k) - n0 :=
    ⟨fun k => (-(b ⟨0, h0⟩ k - a k) - n0).toNat, fun k => (-(-(b ⟨0, h0⟩ k - a k) - n0)).toNat,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hfval : projMap F y w φ (truncCoord t 1) (X ⟨none, l0⟩ * chartMon F M c0 q) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩))) * X none *
        (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ q k)) * tMon q) := by
    rw [map_mul, hXn, projMap_chartMon]
  have hgval : projMap F y w φ (truncCoord t 1) (A0 * chartMon F M c0 p) =
      C (algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0)) *
        tMon (fun _ => n0) * (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ p k)) * tMon p) := by
    rw [map_mul, hA0.2, projMap_chartMon]
  have hprod0 : ∀ r : K → ℕ, ∏ k, y ⟨k, c0 k⟩ ^ r k ≠ 0 :=
    fun r => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (live0 k)
  refine ⟨Pi.single none 1 + liftN q, liftN (fun _ => n0) + liftN p,
    X ⟨none, l0⟩ * chartMon F M c0 q, A0 * chartMon F M c0 p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isMultiHomog_X_none l0).mul (isMultiHomog_chartMon c0 q)
  · exact hA0.1.mul (isMultiHomog_chartMon c0 p)
  · rw [mem_projIdeal_iff, hfval]
    refine mul_ne_zero (mul_ne_zero ?_ (X_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero q))
    · rw [Ne, C_eq_zero]
      exact mul_ne_zero ht0 ((map_ne_zero _).mpr hu0)
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 q)
  · rw [mem_projIdeal_iff, hgval]
    refine mul_ne_zero (mul_ne_zero ?_ (tMon_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero p))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (mul_ne_zero hl0 (pow_ne_zero _ hs0))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 p)
  · funext o
    cases o with
    | none => simp [liftN, zetaDeg, liftDeg]
    | some k =>
      have := hpq k
      simp [liftN, zetaDeg, liftDeg]
      linarith
  · funext W
    show divCycle _ _ W - divCycle _ _ W = 0
    by_cases hW : W.IsPrime ∧ projIdeal F y w φ (truncCoord t 1) ≤ W ∧ IsRelevant W
    · obtain ⟨hWp, hPW, hWrel⟩ := hW
      choose cc hcc using fun k => hWrel (some k)
      let c : ∀ k, ι k := cc
      have hcW : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W := hcc
      obtain ⟨l1, hl1⟩ : ∃ l1 : Fin M, (X ⟨none, l1⟩ : MRing (bundleIdx ι M) F) ∉ W := hWrel none
      have live : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
        intro k h
        apply hcW k
        apply hPW
        rw [mem_projIdeal_iff, projMap_X_some, h, map_zero, C_0, zero_mul]
      have hs := segreVec_ne_zero_of_live live
      obtain ⟨hξ, vc, hvc, hsumc⟩ := chart_data y B w b hB a φ hφ c hs h0
      obtain ⟨nξ, hnξ⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hξ
      obtain ⟨nv, hnv⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hvc
      set m := nξ + nv with hm
      choose Ξ hΞ using hnξ m (by omega)
      choose V hV using hnv m (by omega)
      have htm : (tMon (fun _ : K => m + m) : MvPolynomial (Option K) Φ) =
          tMon (fun _ => m) * tMon (fun _ => m) := tMon_add (fun _ => m) (fun _ => m)
      have hR0 : ∑ l, V l * Ξ l - chartMon F M c (fun _ => m + m) ∈ projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_sum, projMap_chartMon, htm, sub_eq_zero]
        have e1 : ∀ l, projMap F y w φ (truncCoord t 1) (V l * Ξ l) =
            C (algebraMap Ω Φ (vc l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)))) *
              (C (algebraMap Ω Φ (segreVec y c ^ (m + m))) * (tMon (fun _ => m) * tMon (fun _ => m))) := by
          intro l
          rw [map_mul, (hV l).2, (hΞ l).2]
          simp only [map_mul, map_pow, pow_add]
          ring
        rw [Finset.sum_congr rfl (fun l _ => e1 l), ← Finset.sum_mul, ← map_sum, ← map_sum, hsumc,
          map_one, map_one, one_mul]
        simp [segreVec, Finset.prod_pow]
      have hS : chartMon F M c (fun _ => m + m) ∉ W := chartMon_not_mem hcW _
      obtain ⟨l2, hl2⟩ : ∃ l2, Ξ l2 ∉ W := by
        by_contra hcon
        push Not at hcon
        have hsumW : ∑ l, V l * Ξ l ∈ W := Ideal.sum_mem _ fun l _ => W.mul_mem_left _ (hcon l)
        apply hS
        have := W.sub_mem hsumW (hPW hR0)
        rwa [sub_sub_cancel] at this
      have hR1 : X ⟨none, l1⟩ * Ξ l2 - X ⟨none, l2⟩ * Ξ l1 ∈ projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul, map_mul, hXn, hXn, (hΞ l2).2, (hΞ l1).2, sub_eq_zero]
        simp only [map_mul]
        ring
      have h12 : X ⟨none, l1⟩ * Ξ l2 ∉ W := fun h => (hWp.mem_or_mem h).elim hl1 hl2
      have h21 : X ⟨none, l2⟩ * Ξ l1 ∉ W := fun h => h12 (by
        have := W.add_mem (hPW hR1) h
        rwa [sub_add_cancel] at this)
      have hx2 : (X ⟨none, l2⟩ : MRing (bundleIdx ι M) F) ∉ W := fun h => h21 (W.mul_mem_right _ h)
      obtain ⟨α, β, hαβ⟩ : ∃ α β : K → ℕ, ∀ k, (β k : ℤ) - α k = m + (b ⟨0, h0⟩ k - a k) :=
        ⟨fun k => (-(m + (b ⟨0, h0⟩ k - a k))).toNat, fun k => (m + (b ⟨0, h0⟩ k - a k)).toNat,
          fun k => Int.toNat_sub_toNat_neg _⟩
      have hne1 : Ξ l2 * chartMon F M c α ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hl2 (chartMon_not_mem hcW α)
      have hne2 : X ⟨none, l2⟩ * chartMon F M c β ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hx2 (chartMon_not_mem hcW β)
      have hT : (tMon (fun _ => m) * tMon α * tMon q : MvPolynomial (Option K) Φ) =
          tMon β * tMon (fun _ => n0) * tMon p := by
        rw [← tMon_add, ← tMon_add, ← tMon_add, ← tMon_add]
        congr 1
        funext k
        have h1 := hαβ k
        have h2 := hpq k
        simp only [Pi.add_apply]
        omega
      have hc1 : chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m * ∏ k, y ⟨k, c k⟩ ^ α k =
          ∏ k, y ⟨k, c k⟩ ^ β k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live, ← chartZ_add live]
        congr 1
        funext k
        have h1 := hαβ k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hc0 : chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0 * ∏ k, y ⟨k, c0 k⟩ ^ p k =
          ∏ k, y ⟨k, c0 k⟩ ^ q k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live0, ← chartZ_add live0]
        congr 1
        funext k
        have h2 := hpq k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hΩ : φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m *
            (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c0 k⟩ ^ q k) =
          φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
            (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
            (∏ k, y ⟨k, c0 k⟩ ^ p k) := by
        rw [← hc1, ← hc0]
        ring
      have hcross : (Ξ l2 * chartMon F M c α) * (X ⟨none, l0⟩ * chartMon F M c0 q) -
          (X ⟨none, l2⟩ * chartMon F M c β) * (A0 * chartMon F M c0 p) ∈
            projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2 * _),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩ * _), hfval, hgval,
          map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩), (hΞ l2).2, hXn, projMap_chartMon, projMap_chartMon, sub_eq_zero]
        calc _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) *
                segreVec y c ^ m * (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) *
                (∏ k, y ⟨k, c0 k⟩ ^ q k))) * X none * (tMon (fun _ => m) * tMon α * tMon q) := by
              simp only [map_mul]
              ring
          _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
                (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
                (∏ k, y ⟨k, c0 k⟩ ^ p k))) * X none * (tMon β * tMon (fun _ => n0) * tMon p) := by
              rw [hΩ, hT]
          _ = _ := by
              simp only [map_mul]
              ring
      rw [divCycle_eq_of_mul_sub_mem hne1 hne2 hcross, sub_self]
    · have hz : ∀ h, divCycle (projIdeal F y w φ (truncCoord t 1)) h W = 0 := by
        intro h
        by_contra hne
        exact hW (le_and_isRelevant_of_divCycle_ne_zero hne)
      rw [hz, hz, sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end


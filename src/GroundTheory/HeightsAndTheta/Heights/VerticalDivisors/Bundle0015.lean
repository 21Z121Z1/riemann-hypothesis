import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartBack

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFibreDrop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibreDrop.proof : GenericFibreDrop.Statement := by
  intro O _ _ _ F _ _ _ n P P' f hP hP'C hfP hP'
  let A := MvPolynomial (Fin n) O
  let T := MvPolynomial (Fin n) F
  let M : Submonoid A := (nonZeroDivisors O).map (C : O →+* A)
  have hφ : (algebraMap A T) = MvPolynomial.map (algebraMap O F) := rfl
  have : IsLocalization M T := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hP'p : P'.IsPrime := hP'.1.1
  have hPP' : P ≤ P' := le_sup_left.trans hP'.1.2
  have hfP' : f ∈ P' := hP'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hdisj' : Disjoint (M : Set A) (P' : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨o, ho, rfl⟩ hmem
    have h1 : o ∈ P'.comap (C : O →+* A) := hmem
    rw [hP'C, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero ho h1
  have hdisj : Disjoint (M : Set A) (P : Set A) :=
    Set.disjoint_of_subset_right hPP' hdisj'

  let I : Ideal T := P.map (algebraMap A T)
  let I' : Ideal T := P'.map (algebraMap A T)
  have hI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P hP hdisj
  have hI' : I'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P' hP'p hdisj'
  have hII' : I ≤ I' := Ideal.map_mono hPP'

  let Q : Ideal (A ⧸ P) := P'.map (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : Ideal.Quotient.mk P f ∈ Q := Ideal.mem_map_of_mem _ hfP'
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hfP h1
  have hQ1 : Q.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hP') ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQne)
    simpa using this

  let M' : Submonoid (A ⧸ P) := Algebra.algebraMapSubmonoid (A ⧸ P) M
  have hQdisj : Disjoint (M' : Set (A ⧸ P)) (Q : Set (A ⧸ P)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have h1 : Ideal.Quotient.mk P a ∈ Q := hmem
    rw [Ideal.mem_quotient_iff_mem hPP'] at h1
    exact Set.disjoint_left.1 hdisj' ha h1
  have hh := IsLocalization.height_map_of_disjoint (S := T ⧸ I) M' Q hQdisj
  have hmap : Q.map (algebraMap (A ⧸ P) (T ⧸ I)) = I'.map (Ideal.Quotient.mk I) := by
    simp only [Q, I', Ideal.map_map]
    rfl
  rw [hmap, hQ1] at hh
  have _ : (I'.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F
    (I'.map (Ideal.Quotient.mk I))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hII')] at key
  show ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I') + 1
  rw [← key, add_comm]
  rfl

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecPointSeparable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecPointSeparable

theorem isSeparable_of_derivation_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨⟨fun a b => ?_⟩⟩
  have key : ∀ ω : Ω[L⁄K], ω = 0 := by
    intro ω
    refine (Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_
    have : φ = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation K L).injective
      rw [map_zero]
      exact h _
    rw [this, LinearMap.zero_apply]
  rw [key a, key b]

end SecPointSeparable

open SecPointSeparable in
theorem SecPointSeparable.proof (h₁ : GenericFormsKer.Statement) (h₂ : DerivSpanTrdeg.Statement)
    (h₃ : FreeParAlgIndep.Statement) : SecPointSeparable.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hx hU hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0 := by
    by_contra! h
    simp [h] at hT
  set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz
  obtain ⟨r, hre, b, hb⟩ := h₂ k L (Fin n) z e (htr j₀ hj₀)
  have hind := h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars k)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hDK : ∀ a : GenParField k e n, D (algebraMap (GenParField k e n) L a) = 0 :=
    fun a => D.map_algebraMap a
  have hlin : ∀ (a : GenParField k e n) (y : L),
      D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y := by
    intro a y
    rw [D.leibniz, hDK, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e,
      ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
    have := congrArg D h0
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre
      (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hx₀ : D (x j₀) = 0 := by
    have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs
    rw [map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv,
      eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hxj : ∀ j, D (x j) = 0 := by
    intro j
    have hxz : x j = z j * x j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hxz, D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem SpecChart.proof : SpecChart.Statement := by
  intro K _ _ n e I v _ 𝔫 W _ hW h𝔫
  have := 𝔫.isMaximal
  have hPW : integralModel I ≤ W := le_trans le_sup_left hW.1.1.2
  have h𝔫' : W.map (toSecB e I v) = 𝔫.asIdeal := by rw [← secIdealOf_eq_map]; exact h𝔫
  obtain ⟨hcontr, hflat⟩ := SpecChart.contraction_and_flat 𝔫.asIdeal hPW h𝔫'
  have hunit : ∀ s : W.primeCompl, IsUnit (((algebraMap (SecB e I v)
      (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v)) s) := fun s =>
    IsLocalization.map_units (Localization.AtPrime 𝔫.asIdeal)
      (⟨toSecB e I v s, fun h => s.2 (hcontr _ h)⟩ : 𝔫.asIdeal.primeCompl)
  let ψ0 : Localization.AtPrime W →+* Localization.AtPrime 𝔫.asIdeal :=
    IsLocalization.lift (M := W.primeCompl) hunit
  have hψ0 : ∀ g, ψ0 (algebraMap _ (Localization.AtPrime W) g) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) :=
    fun g => IsLocalization.lift_eq hunit g
  have hker : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker ψ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ0, RingHom.mem_ker.mp (SpecChart.toSecB_le e hg), map_zero]
  have hker' : ∀ a ∈ (integralModel I).map (algebraMap _ (Localization.AtPrime W)), ψ0 a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hker ha)
  let ψ := Ideal.Quotient.lift _ ψ0 hker'
  have hψ : ∀ g, ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
      algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (toSecB e I v g) := fun g => by
    show Ideal.Quotient.lift _ ψ0 hker' (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, hψ0]
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal) := by
    have hcomp : (ψ.comp (Ideal.Quotient.mk _)).comp (algebraMap _ (Localization.AtPrime W)) =
        (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)).comp (toSecB e I v) :=
      RingHom.ext fun g => hψ g
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := W), Ideal.map_map, hcomp, ← Ideal.map_map, h𝔫',
      Localization.AtPrime.map_eq_maximalIdeal]
  refine ⟨ψ, fun g => ?_, ?_, ?_, hmax⟩
  · rw [hψ]
    rfl
  · exact ((IsLocalRing.local_hom_TFAE (ψ.comp (Ideal.Quotient.mk _))).out 2 0).mp hmax.le
  · have := SpecChart.isLocalization_quot W (integralModel I)
    refine SpecChart.flat_of_isLocalization_comp (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
      (S := Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
      (T := Localization.AtPrime 𝔫.asIdeal) (W.primeCompl.map (Ideal.Quotient.mk (integralModel I))) ψ ?_
    have h : ψ.comp (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I)
        (Localization.AtPrime W ⧸ (integralModel I).map (algebraMap _ (Localization.AtPrime W)))) =
        SpecChart.quotToBn e 𝔫.asIdeal := by
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hψ, SpecChart.quotToBn_mk]
    rw [h]
    exact hflat

end

end GroundTheory.Heights₂.Heights.Vertical
end


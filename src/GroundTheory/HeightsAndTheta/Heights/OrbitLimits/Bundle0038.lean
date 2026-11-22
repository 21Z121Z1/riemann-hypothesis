import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem genFibreExists : GenFibreExistsStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' _ hP'
  exact Inter.GenericPointExists.proof K ι K' ι' v P' hP'.2.1.1

theorem existsUniqueAll : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)], ExistsUniqueStatement F ι := by
  intro F _ K _ ι _
  exact ExistsUnique.full F ι

theorem ChangeOfModel.of_found (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hIso : HilbertSamuel.IsomInvariance.Statement) (hGI : HilbertSamuel.GraphIsometric.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
  HilbertSamuel.ChangeOfModel.proof hAI3 hGr genFibreExists existsUniqueAll hIso hGI

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImportsBis
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjMaxRankMeetsPsi0.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val →
    ∀ y ∈ projMaxRank R Ψ BV, ∃ y' ∈ connectedComponent y,
      y' ∈ projMaxRank R Ψ BV ∧ Ψ (segre (R.lift y'.1 y'.1)) 0 ≠ 0

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

theorem MoriwakiHS.of_open (hC : KH.CondStatement) (hG : GridSeparation.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement)
    (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement :=
  MoriwakiHS.of_leaves hC hG RelSectionsLarge.full hL2 hP hM hS hApx hCurve

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem proof : ComponentsGenericCount.Statement := by
  classical
  intro n d F A hF hinc
  have hfib : ∀ y, {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} = ⋃ J ∈ F, fibre J A y := by
    intro y; ext x; simp only [fibre, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]; tauto
  have hcard : ∀ J ∈ F, ∀ y, (fibre J A y).encard ≤ (projDegree J A : ℕ∞) := by
    intro J hJ y
    obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2 y
    rw [← hfin.cast_ncard_eq]; exact_mod_cast hle
  refine ⟨fun y => ?_, ?_⟩
  · rw [hfib, Nat.cast_sum]
    exact (encard_biUnion_le F _).trans (Finset.sum_le_sum fun J hJ => hcard J hJ y)
  obtain ⟨Δ₁, hΔ₁, hΔ₁y⟩ := exists_prod_ne_zero F
    (fun J P => ∀ y, eval y P ≠ 0 → (fibre J A y).Finite ∧ (fibre J A y).ncard = projDegree J A ∧
      ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
        DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ g y' ∈ zeroSet J)
    (fun J hJ => by
      obtain ⟨P, hP, hPy⟩ :=
        ComplexSets.DiscriminantCover.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2
      refine ⟨P, hP, fun y hy => ?_⟩
      obtain ⟨hfin, hc, hsec⟩ := hPy y hy
      refine ⟨hfin, hc, fun x hx => ?_⟩
      obtain ⟨U, V, g, hU, hyU, -, -, hg, hgx, hAg, hZ⟩ := hsec x hx
      refine ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨hAg y' hy', ?_⟩⟩
      have hmem : g y' ∈ zeroSet J ∩ V := hZ ▸ Set.mem_image_of_mem g hy'
      exact hmem.1)
  obtain ⟨Δ₂, hΔ₂, hΔ₂y⟩ := exists_prod_ne_zero ((F ×ˢ F).filter fun p => p.1 ≠ p.2)
    (fun p c => ∀ x ∈ zeroSet p.1, x ∈ zeroSet p.2 → eval (A *ᵥ x) c = 0)
    (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact exists_pair_poly p.1 p.2 A (hF _ hp.1.1).1 (hF _ hp.1.1).2.2
        fun h => hp.2 (hinc _ hp.1.2 _ hp.1.1 h).symm)
  refine ⟨Δ₁ * Δ₂, mul_ne_zero hΔ₁ hΔ₂, fun y hy => ?_⟩
  rw [map_mul] at hy
  have h1 := hΔ₁y y (left_ne_zero_of_mul hy)
  have h2 := hΔ₂y y (right_ne_zero_of_mul hy)
  refine ⟨?_, ?_⟩
  · rw [hfib, Nat.cast_sum, encard_biUnion_eq]
    · refine Finset.sum_congr rfl fun J hJ => ?_
      obtain ⟨P, hP, hPy⟩ := h1 J hJ
      obtain ⟨hfin, hc, -⟩ := hP y hPy
      rw [← hfin.cast_ncard_eq, hc]
    · intro J hJ J' hJ' hne
      rw [Set.disjoint_left]
      rintro x ⟨hxJ, hxy⟩ ⟨hxJ', -⟩
      obtain ⟨c, hc, hcy⟩ := h2 (J, J') (by simp [hJ, hJ', hne])
      exact hcy (by rw [← hxy]; exact hc x hxJ hxJ')
  · rintro x ⟨J, hJ, hxJ⟩ hxy
    obtain ⟨P, hP, hPy⟩ := h1 J hJ
    obtain ⟨U, g, hU, hyU, hg, hgx, hsec⟩ := (hP y hPy).2.2 x ⟨hxJ, hxy⟩
    exact ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨(hsec y' hy').1, J, hJ, (hsec y' hy').2⟩⟩

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ConeSliceIdeal.proof : ConeSliceIdeal.Statement := by
  intro n C t V hC hV f hf
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  obtain ⟨G, D, hG, hGf⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) f hℓ
  have hLG : linForm t * G ∈ V := by
    refine hV ?_
    rw [mem_vanishingIdeal_iff]
    intro c hc
    show eval c (linForm t * G) = 0
    rw [map_mul]
    by_cases hl : eval c (linForm t) = 0
    · rw [hl, zero_mul]
    · set l := eval c (linForm t)
      have hsl : eval (l⁻¹ • c) (linForm t) = 1 := by
        rw [GoodChartZeroSet.eval_smul_of_isHomogeneous hℓ, pow_one, inv_mul_cancel₀ hl]
      have hmem : l⁻¹ • c ∈ {x | x ∈ C ∧ eval x (linForm t) = 1} :=
        ⟨hC c hc _ (inv_ne_zero hl), hsl⟩
      have hf0 : eval (l⁻¹ • c) f = 0 := (mem_vanishingIdeal_iff.mp hf) _ hmem
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hGf
      have hGv : eval (l⁻¹ • c) G = 0 := by
        have h := congrArg (eval (l⁻¹ • c)) hq
        rw [map_sub, map_mul, map_sub, hsl, hf0, map_one] at h
        simpa using h
      have hc' : c = l • (l⁻¹ • c) := by rw [smul_smul, mul_inv_cancel₀ hl, one_smul]
      rw [hc', GoodChartZeroSet.eval_smul_of_isHomogeneous hG, hGv, mul_zero, mul_zero]
  have e : f = linForm t * G - (linForm t - 1) * G - (G - f) := by ring
  rw [e]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left hLG) ?_) (Ideal.mem_sup_right hGf)
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

theorem ConeVanishingHomog.proof : ConeVanishingHomog.Statement := by
  intro n C hC f hf d
  rw [mem_vanishingIdeal_iff] at hf ⊢
  intro c hc
  replace hf : ∀ x ∈ C, eval x f = 0 := hf
  show eval c (homogeneousComponent d f) = 0

  set p : Polynomial ℂ := ∑ i ∈ range (f.totalDegree + 1),
    Polynomial.C (eval c (homogeneousComponent i f)) * Polynomial.X ^ i with hp
  have hroot : ∀ a : ℂ, a ≠ 0 → p.IsRoot a := by
    intro a ha
    have h0 := hf (a • c) (hC c hc a ha)
    rw [← sum_homogeneousComponent f, map_sum] at h0
    rw [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GoodChartZeroSet.eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i f)]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    refine Set.Infinite.mono (fun x hx => hroot x hx) ?_
    exact (Set.finite_singleton (0 : ℂ)).infinite_compl
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hinf
  by_cases hd : d ≤ f.totalDegree
  · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hp0
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    simpa [Finset.mem_range, Nat.lt_succ_of_le hd] using hcoeff
  · rw [homogeneousComponent_eq_zero d f (by omega), map_zero]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem CoordFibreDeg.proof (hM : FibreMultiHomog.Statement) (hD : GenFibreChartDeg.Statement)
    (hR : CoordRatioDeg.Statement) : CoordFibreDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y d G i hb hZ' hZ hi
  have : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa using hn
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
    simpa using hmem
  have hMH : IsMultiHomogIdeal (mCoordIdeal y) := hZ'.2.1.2.1
  choose c hc using hZ.2.1.2.2
  have hx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by
    rw [← G.ker_x, RingHom.mem_ker, aeval_X]
    exact h)
  have hi' : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h)
  have h1 := Inter.ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ'
    (fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩) i hi'
    (hM K ι K' ι' κ v (mCoordIdeal y) G hb hMH)
  exact h1.trans ((hD K ι K' ι' κ v (mCoordIdeal y) G c i hb hMH hx hi').trans
    (hR K ι K' ι' κ v Ω y G.Φ' G.x' hb G.genericFibre_ker_target))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace CoordRatioDeg

def ratioField {S M : Type*} [Field M] [CharZero M] (R : S → S → Prop) (z : S → M) : IntermediateField ℚ M :=
  IntermediateField.adjoin ℚ {t | ∃ p q, R p q ∧ t = z p / z q}

theorem ratioField_map {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by
  rw [ratioField, IntermediateField.adjoin_map, ratioField]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp⟩
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp⟩

theorem ratioField_congr {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by
  unfold ratioField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, h p q hpq⟩
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, (h p q hpq).symm⟩

theorem proof : CoordRatioDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker
  let I : Ideal (MRing ι') := mCoordIdeal y
  let L := FractionRing (MvPolynomial K' Ω)
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)
  have h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0 := fun a ha => by
    rw [show I = _ from hker.symm] at ha
    exact RingHom.mem_ker.mp ha
  have h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  let g₁ : MRing ι' ⧸ I →+* Φ' := Ideal.Quotient.lift I _ h₁
  have hg₁ : Function.Injective g₁ :=
    RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by
      change a ∈ mCoordIdeal y
      rw [← hker]
      exact ha
  let g₂ : MRing ι' ⧸ I →+* L := (algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)
  have hg₂ : Function.Injective g₂ :=
    (IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)
  have : IsDomain (MRing ι' ⧸ I) := hg₁.isDomain g₁
  let F := FractionRing (MRing ι' ⧸ I)
  let f₁ : F →+* Φ' := IsFractionRing.lift hg₁
  have : CharZero F := ⟨fun m n h => by
    have h' := congrArg f₁ h
    rw [map_natCast, map_natCast] at h'
    exact_mod_cast h'⟩
  let f₂ : F →+* L := IsFractionRing.lift hg₂
  let xb : (Σ k', ι' k') → F := fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))
  have e₁ : f₁.toRatAlgHom ∘ xb = x' := funext fun p => by
    simp [xb, f₁, g₁, IsFractionRing.lift_algebraMap]
  have e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1) := fun p => by
    simp [xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]
  let c : Ω →ₐ[ℚ] L := ((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom
  have hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)
  have hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q) := by
    intro p q h
    rw [e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]
    rfl
  change IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') =
    IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)
  rw [← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁,
    Function.comp_assoc, ← ratioField_map, ← ratioField_map,
    IntermediateField.relfinrank_map_map,
    ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]
  congr 1
  · refine ratioField_congr fun p q h => ?_
    simpa using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])
  · exact ratioField_congr fun p q h => by simpa using hr p q h

end CoordRatioDeg

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjFullRankDense
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ProjFullRankDense.of_found (hOpen : ProjRegularClosureOpen.Statement)
    (hMeet : ProjFullRankMeetsRegular.Statement) : ProjFullRankDense.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hMeet K ι P J n R Ψ V BV hH hC hΨ x hx
  have hO : IsOpen (closure (projRegular R Ψ BV)) := hOpen K ι P J n R Ψ V BV hH
  have hcl : IsClopen (closure (projRegular R Ψ BV)) := ⟨isClosed_closure, hO⟩
  rw [hO.interior_eq]
  have hsub := hcl.connectedComponent_subset (subset_closure hy)
  rw [← connectedComponent_eq hyc] at hsub
  exact hsub mem_connectedComponent

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushResFibreGerms
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Topology Filter ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def resAbove {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e n : ℕ}
    (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) : Set R.X :=
  {x | projCoord R Ψ x = y ∧ divPt R Ψ x = w}

def DivPushResFibreGerms.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (A : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∀ Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ f ∈ Wa, eval z f = 0) → segre z = w →
        (resAbove R Ψ y w).Finite ∧
        ∃ V : R.X → Set R.X,
          (∀ x ∈ resAbove R Ψ y w, IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ R.U x) ∧
          (∀ x ∈ resAbove R Ψ y w, ∀ k k', x ∈ W k → x ∈ W k' → k = k') ∧
          (∀ x ∈ resAbove R Ψ y w, ∀ y₁ ∈ V x, ∀ y₂ ∈ V x,
            SameOrbit (R.lift x y₁) (R.lift x y₂) → y₁ = y₂) ∧
          (∀ x ∈ resAbove R Ψ y w, ∀ x' ∈ resAbove R Ψ y w, x ≠ x' → ∀ v : (Σ k, ι k) → ℂ,
            (∃ y₁ ∈ V x, SameOrbit v (R.lift x y₁)) → (∃ y₂ ∈ V x', SameOrbit v (R.lift x' y₂)) →
              eval v (map (Int.castRingHom ℂ) s) = 0) ∧
          (∀ V' : R.X → Set R.X, (∀ x ∈ resAbove R Ψ y w, V' x ∈ 𝓝 x) →
            ∃ N ∈ 𝓝 z, ∀ v ∈ mcPts P ∩ N, ∃ x ∈ resAbove R Ψ y w, ∃ y₁ ∈ V' x ∩ V x,
              SameOrbit v (R.lift x y₁)) ∧
          (∀ V' : R.X → Set R.X, (∀ x ∈ resAbove R Ψ y w, V' x ∈ 𝓝 x) →
            ∃ N ∈ 𝓝 z, ∀ v ∈ N, (∀ f ∈ Wa, eval v f = 0) → ∀ x ∈ resAbove R Ψ y w,
              ∃ y₁ ∈ V' x ∩ V x, eval (R.lift x y₁) (map (Int.castRingHom ℂ) s) = 0 ∧
                SameOrbit v (R.lift x y₁))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjMaxRankRegular
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjMaxRankRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val →
    ∀ y ∈ projMaxRank R Ψ BV, Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0 → y ∈ projRegular R Ψ BV

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def multiprojPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e : ℕ} (R : AnLogRes P J e) (V : Set R.X) : LocPot V where
  U y := Subtype.val ⁻¹' R.U y.1
  isOpen_U y := (R.isOpen_U y.1).preimage continuous_subtype_val
  mem_U y := R.mem_U y.1
  φ y z := ∑ k, Real.log (∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)

def projPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e m : ℕ} (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ))
    (V : Set R.X) : LocPot V where
  U y := Subtype.val ⁻¹' R.U y.1
  isOpen_U y := (R.isOpen_U y.1).preimage continuous_subtype_val
  mem_U y := R.mem_U y.1
  φ y z := Real.log (∑ l, ‖Ψ (segre (R.lift y.1 z.1)) l‖ ^ 2)

def ProjPotMassEq.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ C : Set V, IsClopen C →
      mInt BV (fun _ => multiprojPot R V) (C.indicator fun _ => (1 : ℝ)) =
        mInt BV (fun _ => projPot R Ψ V) (C.indicator fun _ => (1 : ℝ))

end GroundTheory.Heights₂.Heights.Targets
end
end


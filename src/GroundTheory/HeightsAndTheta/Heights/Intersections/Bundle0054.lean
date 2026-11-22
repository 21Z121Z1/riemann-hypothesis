import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalize.exists_prime_over {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hW : IsClosedPt W) :
    ∃ p : ℤ, Prime p ∧ ∀ k : ℤ, C k ∈ W ↔ p ∣ k := by
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  have : W.IsPrime := hW.1.1
  have : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.IsPrime.comap _
  refine ⟨_, Submodule.IsPrincipal.prime_generator_of_isPrime _ hvert, fun k => ?_⟩
  rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap]

theorem RegularityLocalize.proof (h₁ : RegularityLocalPrime.Statement) : RegularityLocalize.Statement := by
  classical
  intro K _ ι _ P W y hP hW hPW hy
  have hPp : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1
  have hφ : ∀ f : MRing ι, f ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0 :=
    fun f hf => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hf
  obtain ⟨p, hp, hpW⟩ := RegularityLocalize.exists_prime_over hP hW
  have hCpP : (C p : MRing ι) ∉ P := fun h => hp.ne_zero (by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rwa [hP.2.2.1, Ideal.mem_bot] at h')

  set S : Set (Ideal (MRing ι)) := {W' | IsClosedPt W' ∧ P ≤ W' ∧ C p ∈ W'} with hS
  have hSfin : S.Finite := (divSupp_finite P (C p)).subset fun W' hW' =>
    (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W' hP (RegularityDenominator.isMultiHomog_C p) hCpP).2 hW'
  have hWS : W ∈ S := ⟨hW, hPW, (hpW p).2 dvd_rfl⟩
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSfin fun W' hW' => hW'.1.1

  obtain ⟨u₀, v₀, a, hu₀, hv₀, hv₀W, hyv₀⟩ := LocRingFrac.proof K ι P W hPp hWp hPW y hy
  choose c hc using hW.1.2.2
  obtain ⟨t, ht, htW⟩ : ∃ t : MRing ι, IsMultiHomog t 1 ∧ t ∉ W :=
    ⟨_, AvoidRing.isMultiHomog_coordProd c 1, AvoidRing.coordProd_not_mem hWp c hc 1⟩
  obtain ⟨u, v, hu, hv, hvW, hyv⟩ : ∃ u v : MRing ι, IsMultiHomog u (a + 1) ∧ IsMultiHomog v (a + 1) ∧ v ∉ W ∧
      y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) :=
    ⟨u₀ * t, v₀ * t, AvoidRing.isMultiHomog_mul hu₀ ht, AvoidRing.isMultiHomog_mul hv₀ ht,
      fun h => (hWp.mem_or_mem h).elim hv₀W htW, by simp only [map_mul, ← mul_assoc, hyv₀]⟩

  set m := ∑ k, d₀ k
  obtain ⟨h, hh, hhS⟩ := hd₀ ((m + 1) • (a + 1)) fun k => by
    have h1 : d₀ k ≤ m := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    nlinarith
  have hhW : h ∉ W := hhS W hWS
  have hhP : h ∉ P := fun e => hhW (hPW e)
  have hvm : IsMultiHomog (v ^ (m + 1)) ((m + 1) • (a + 1)) := AvoidRing.isMultiHomog_pow hv _
  have hxm : IsMultiHomog (v ^ m * u) ((m + 1) • (a + 1)) := by
    rw [succ_nsmul]; exact AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_pow hv _) hu
  obtain ⟨s₀, hs₀⟩ := exists_funField_mul_eq hvm hh hhP
  obtain ⟨x₀, hx₀⟩ := exists_funField_mul_eq hxm hh hhP
  have hys : y * (s₀ : FractionRing (MRing ι ⧸ P)) = x₀ := by
    refine mul_right_cancel₀ (hφ h hhP) ?_
    rw [mul_assoc, hs₀, hx₀]
    simp only [map_pow, map_mul]
    rw [pow_succ, ← hyv]
    ring

  have hover : ∀ z : funField P, (∃ g : MRing ι, IsMultiHomog g ((m + 1) • (a + 1)) ∧
      (z : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P h) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
      ∀ W', IsClosedPt W' → P ≤ W' → C p ∈ W' → (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W' :=
    fun z ⟨g, hg, hz⟩ W' h1 h2 h3 => frac_mem_locRing h2 hg hh (hhS W' ⟨h1, h2, h3⟩) hz
  obtain ⟨n₁, hn₁, hs⟩ := h₁ K ι P p s₀ hP hp (hover s₀ ⟨_, hvm, hs₀⟩)
  obtain ⟨n₂, hn₂, hx⟩ := h₁ K ι P p x₀ hP hp (hover x₀ ⟨_, hxm, hx₀⟩)
  have hsc : (((n₂ : regRing P) * ⟨_, hs⟩ : regRing P) : funField P) = (n₂ : funField P) * ((n₁ : funField P) * s₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  have hxc : (((n₁ : regRing P) * ⟨_, hx⟩ : regRing P) : funField P) = (n₁ : funField P) * ((n₂ : funField P) * x₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  refine ⟨(n₂ : regRing P) * ⟨_, hs⟩, (n₁ : regRing P) * ⟨_, hx⟩, ?_, ?_⟩
  ·
    have hnW : (C (n₁ * n₂) : MRing ι) ∉ W := fun e => by
      rcases hp.dvd_or_dvd ((hpW _).1 e) with h' | h'
      exacts [hn₁ h', hn₂ h']
    have hden : IsMultiHomog (C (n₁ * n₂) * v ^ (m + 1)) ((m + 1) • (a + 1)) := by
      simpa using AvoidRing.isMultiHomog_mul (RegularityDenominator.isMultiHomog_C (n₁ * n₂)) hvm
    have hdenW : C (n₁ * n₂) * v ^ (m + 1) ∉ W := fun e =>
      (hWp.mem_or_mem e).elim hnW fun e' => hvW (hWp.mem_of_pow_mem _ e')
    have hden0 := hφ _ fun e => hdenW (hPW e)
    refine ⟨_, frac_mem_locRing hPW hh hden hdenW (div_mul_cancel₀ _ hden0), ?_⟩
    rw [hsc, mul_div_assoc', div_eq_one_iff_eq hden0]
    simp only [map_mul, eq_intCast C, map_intCast, Int.cast_mul, Subring.coe_mul, Subring.coe_intCast, ← hs₀]
    ring
  · rw [hsc, hxc]
    simp only [Subring.coe_mul, Subring.coe_intCast, ← hys]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreRest
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ArithmeticIntersectionChartFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    FiniteDimensional G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreSide
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ChartNormCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    FiniteDimensional G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) →
    ∃ E : MRing ι, E ∉ imageZ v P' ∧
      ∀ w ∈ mcPts (imageZ v P'), eval w (map (Int.castRingHom ℂ) E) ≠ 0 →
        {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1}.Finite ∧
        {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1}.ncard =
          Module.finrank G.Φ (IntermediateField.adjoin G.Φ
            (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) ∧
        ∀ z' ∈ mcPts P', (∀ p, z' (v p) = w p) → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
          ∀ q : Σ k : FibreBlock κ, ι' k.1, G.x' ⟨q.1.1, q.2⟩ ≠ 0 → z' ⟨q.1.1, q.2⟩ ≠ 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTer
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDimensionZero.proof (h₁ : ArithmeticIntersectionFibreMultiHomogeneous.Statement) (h₂ : EvalKerKrullDim.Statement)
    (h₃ : FibreTranscendenceDegreeAlt.Statement) : FibreDimensionZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  refine ⟨⟨RingHom.ker_isPrime _, h₁ K ι K' ι' κ v p W' hv hp hW.1.2.1 G', fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hW.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    have hX : (X ⟨k.1, i⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  · rw [fibreIdeal, h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ', h₃ K ι K' ι' κ v p W' n hv hp hW hV G']
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogProdInt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsAvoidBadLocus

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] in

theorem isMultiHomog_prod_int {β : Type*} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm k
    rw [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    intro m hm k
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    have h1 := h b (Finset.mem_insert_self b s) m1 hm1 k
    have h2 := ih (fun b' hb' => h b' (Finset.mem_insert_of_mem hb')) m2 hm2 k
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, h1, h2]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem adjoin_chart_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
    (G : GenFibre v P') (i j : ∀ k : FibreBlock κ, ι' k.1) (hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) :
    IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) ≤
      IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have hq : G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ =
      (G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) / (G.x' ⟨q.1.1, j q.1⟩ / G.x' ⟨q.1.1, i q.1⟩) :=
    (div_div_div_cancel_right₀ (hi q.1) _ _).symm
  show G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ ∈ _
  rw [hq]
  exact div_mem (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    (IntermediateField.subset_adjoin _ _ ⟨⟨q.1, j q.1⟩, rfl⟩)

end GenericPointsAvoidBadLocus

open GenericPointsAvoidBadLocus in

theorem GenericPointsAvoidBadLocus.proof (hChart : GenericPointsInAffineChart.Statement) : GenericPointsAvoidBadLocus.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G i hv hP' hZ hi
  classical
  let C := {j : ∀ k : FibreBlock κ, ι' k.1 // ∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0}
  choose D a hD hDZ hpts using fun j : C => hChart K ι K' ι' κ v P' n G j.1 hv hP' hZ j.2
  have hprime : (imageZ v P').IsPrime := hZ.2.1.1
  refine ⟨∏ j, D j, ∑ j, a j, isMultiHomog_prod_int _ _ _ fun j _ => hD j, fun hmem => ?_, ?_⟩
  · obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hDZ j hj
  intro z hz hDz
  have hDj : ∀ j : C, eval z (map (Int.castRingHom ℂ) (D j)) ≠ 0 := by
    intro j h0
    apply hDz
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h0
  let i0 : C := ⟨i, hi⟩
  have hEq : ∀ j : C, ptsOverChart P' κ v i z = ptsOverChart P' κ v j.1 z := by
    intro j
    have hci : (ptsOverChart P' κ v i z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) :=
      (hpts i0 z hz (hDj i0)).2.1
    obtain ⟨hfin, hcj, -⟩ := hpts j z hz (hDj j)
    have hsub : ptsOverChart P' κ v i z ⊆ ptsOverChart P' κ v j.1 z := by
      rintro O ⟨z', hz', rfl, hw, hc⟩
      exact ⟨z', hz', rfl, hw, fun k => (hpts i0 z hz (hDj i0)).2.2 z' hz' hw hc ⟨k, j.1 k⟩ (j.2 k)⟩
    refine Set.eq_of_subset_of_ncard_le hsub (le_of_eq ?_) hfin
    rw [hcj, hci, le_antisymm (adjoin_chart_le G i j.1 hi) (adjoin_chart_le G j.1 i j.2)]
  have hall : ptsOverPt P' v z = ptsOverChart P' κ v i z := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hw⟩
      choose ℓ hℓ using fun k : FibreBlock κ => hz'.1 k.1
      have hgen : ∀ k : FibreBlock κ, G.x' ⟨k.1, ℓ k⟩ ≠ 0 := by
        intro k h0
        apply hℓ k
        have hmem : (X ⟨k.1, ℓ k⟩ : MRing ι') ∈ P' := by
          rw [← G.genericFibre_ker_target, RingHom.mem_ker]
          simpa using h0
        simpa using hz'.2 _ hmem
      rw [hEq ⟨ℓ, hgen⟩]
      exact ⟨z', hz', rfl, hw, hℓ⟩
    · rintro ⟨z', hz', rfl, hw, -⟩
      exact ⟨z', hz', rfl, hw⟩
  rw [hall]
  exact (hpts i0 z hz (hDj i0)).2.1

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LiftZComponent
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace FibreMultiHomogeneous

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem component_map {σ R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S) (w : σ → ℕ) (n : ℕ)
    (F : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (map g F) = map g (weightedHomogeneousComponent w n F) := by
  ext m
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem component_mem [Fintype K'] [∀ k, Fintype (ι' k)] {p : ℕ} {W' : Ideal (MRing ι')} (hp : ((p : ℕ) : MRing ι') ∈ W')
    (hW : IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) [DecidableEq K'] (k : K')
    (n : ℕ) {g : MRing ι'} (hg : g ∈ W') : weightedHomogeneousComponent (cycBlockWt k) n g ∈ W' := by
  rw [← PointVertical.mem_map_red_iff p hp, PointVertical.red, ← component_map]
  exact weightedHomogeneousComponent_mem_of_mem _ _ (cyc_isHomogeneous_of_isMultiHomogIdeal hW k)
    ((PointVertical.mem_map_red_iff p hp g).2 hg) n

theorem exists_clear [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W') {τ : Type*}
    (f : MvPolynomial τ G.Φ) : ∃ b : MRing ι, aeval G.x b ≠ 0 ∧
      ∃ F : MvPolynomial τ (MRing ι), C (aeval G.x b) * f = map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    obtain ⟨a, b, hb, rfl⟩ := G.gen c
    refine ⟨b, hb, monomial m a, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp
  | add f g hf hg =>
    obtain ⟨b₁, hb₁, F₁, e₁⟩ := hf
    obtain ⟨b₂, hb₂, F₂, e₂⟩ := hg
    refine ⟨b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, C b₂ * F₁ + C b₁ * F₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e₁, ← e₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring

def liftZ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* MRing ι' :=
  eval₂Hom (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom fun q => X ⟨q.1.1, q.2⟩

theorem aeval_liftZ [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W')
    (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    aeval G.x' (liftZ κ v F) = aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)
      (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F) := by
  have h : (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom.comp (liftZ κ v) =
      (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)).toRingHom.comp
        (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · have e : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftZ, coe_eval₂Hom, eval₂_C,
        MvPolynomial.map_C, aeval_C]
      rw [aeval_rename, e, aeval_algebraMap_apply]
    · simp [liftZ]
  exact DFunLike.congr_fun h F

theorem liftZ_component [Fintype K'] [∀ k, Fintype (ι' k)] [DecidableEq K'] {κ : K → K'} [DecidableEq (FibreBlock κ)] {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) (k : FibreBlock κ) (n : ℕ) (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) =
      liftZ κ v (weightedHomogeneousComponent (cycBlockWt k) n F) := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp only [map_add, hF, hG]
  | monomial m a =>
    have hj : ∀ q : Σ k : FibreBlock κ, ι' k.1,
        cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩ = cycBlockWt (ι := fun k : FibreBlock κ => ι' k.1) k q := by
      intro q
      simp only [cycBlockWt, Subtype.ext_iff]
    have h0 : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1) (rename v a) 0 := by
      intro d hd
      obtain ⟨u, rfl, -⟩ : ∃ u, u.mapDomain v = d ∧ coeff u a ≠ 0 := by
        by_contra! h
        exact hd (coeff_rename_eq_zero _ _ _ h)
      rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
      refine Finset.sum_eq_zero fun q _ => ?_
      have : (v q).1 ≠ k.1 := fun h => k.2 ⟨q.1, by rw [← hv.2.2.1 q, h]⟩
      simp [cycBlockWt, this]
    have h1 : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1)
        (m.prod fun q e => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ e) (Finsupp.weight (cycBlockWt k) m) := by
      rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
      convert IsWeightedHomogeneous.prod m.support (fun q => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ m q)
        (fun q => m q • cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩)
        (fun q _ => (isWeightedHomogeneous_X ℤ _ _).pow (m q)) using 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hj]
    have hw : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1) (liftZ κ v (monomial m a))
        (Finsupp.weight (cycBlockWt k) m) := by
      have := h0.mul h1
      rw [zero_add] at this
      simpa [liftZ, eval₂_monomial] using this
    by_cases h : Finsupp.weight (cycBlockWt k) m = n
    · subst h
      rw [hw.weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_same]
    · rw [hw.weightedHomogeneousComponent_ne _ (Ne.symm h),
        (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_ne _ (Ne.symm h), map_zero]

end FibreMultiHomogeneous

open FibreMultiHomogeneous in

theorem ArithmeticIntersectionFibreMultiHomogeneous.proof : ArithmeticIntersectionFibreMultiHomogeneous.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' hv hp hW G'
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G'.Φ (cycBlockWt k)) f n : MvPolynomial _ G'.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G' f
  rw [fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ W' := by
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc := component_mem hp hW k.1 n hF
  rw [liftZ_component hv, ← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PEvalKerKrullDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IntermediateField.algebraAdjoinAdjoin

theorem EvalKerKrullDim.proof : EvalKerKrullDim.Statement := by
  intro K _ ι _ F L _ _ _ y

  let f : MRingOver F ι →ₐ[F] Algebra.adjoin F (Set.range y) :=
    (Subalgebra.equivOfEq _ _ (MvPolynomial.aeval_range y)).toAlgHom.comp (aeval y).rangeRestrict
  have hf : Function.Surjective f :=
    (Subalgebra.equivOfEq _ _ (MvPolynomial.aeval_range y)).surjective.comp
      (AlgHom.rangeRestrict_surjective _)
  have hker : RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L) = RingHom.ker f := by
    ext p
    simp [f, RingHom.mem_ker, Subtype.ext_iff]
  let e : (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) ≃ₐ[F]
      Algebra.adjoin F (Set.range y) :=
    (Ideal.quotientEquivAlgOfEq F hker).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  have _ : Algebra.FiniteType F (Algebra.adjoin F (Set.range y)) :=
    Algebra.FiniteType.of_surjective f hf
  exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing F
    (IntermediateField.adjoin F (Set.range y))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLength
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocLength.proof (h₁ : SemilocLengthSum.Statement) (h₂ : FibreDivSupp.Statement)
    (h₃ : regularityDehomogenization_holds.Statement) : SemilocLength.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have hfib := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨-, N, hN, hsum⟩ := h₁ K ι K' ι' κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy
    (fun W' hW' hsW' => hE W' ((hfib W').1 ⟨hW', hsW'⟩).1 ((hfib W').1 ⟨hW', hsW'⟩).2)
  refine ⟨N, hN, hsum.trans (finsum_mem_congr (Set.ext fun W' => hfib W') fun W' hW' => ?_)⟩
  obtain ⟨hW'd, hW'i⟩ := hW'
  have hs' : rename v s ∉ P' := hsP
  have ht' : rename v t ∉ W' := fun h => htW (hW'i ▸ h)
  have hy' : fracMapZ v P' y * algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk P' (rename v t)) =
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (rename v s)) := by
    rw [← fracMapZ_algebraMap, ← fracMapZ_algebraMap, ← map_mul, hy]
  rw [(h₃ K' ι' P' (rename v s) (rename v t) (Function.extend κ α 0) W' (fracMapZ v P' y) hP'.2.1
    (rename_isMultiHomog hv hs) hs' hW'd (rename_isMultiHomog hv ht) ht' hy').2]

end GroundTheory.Heights₂.Heights.Inter
end
end


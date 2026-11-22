import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IdDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionDivisorPushforward.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ W' ∈ divSupp P' (rename v s), imageZ v W' = W →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0) →
    ∑ᶠ W' ∈ {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W},
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
      J (fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W

section Inhabitants

open Classical in

def idDeg (W' : Ideal (MRing (GlobalTheory 2))) : ℤ :=
  if h : W'.IsPrime then
    haveI := h
    noBlockFam (genFibreIdOf W').Φ (fibreIdx (GlobalTheory 2) (id : Unit → Unit))
      (fibreIdeal id (genFibreIdOf W')) 0 Fin.elim0
  else 0

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDenominator.isMultiHomog_C {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (n : ℤ) :
    IsMultiHomog (C n : MRing ι) 0 := by
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := by simpa using support_monomial_subset hm
  simp [this]

theorem RegularityDenominator.proof (hD : RegularityDivisorSupportClosed.Statement) (hPow : LocRingPow.Statement) :
    RegularityDenominator.Statement := by
  intro K _ ι _ P x hP
  have hPp : P.IsPrime := hP.2.1.1
  have hFL : (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := x.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hva, hvP, hxv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL

  have key : ∀ W ∈ divSupp P v, ∃ m : ℤ, m ≠ 0 ∧
      (x : FractionRing (MRing ι ⧸ P)) * (m : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    intro W hW
    obtain ⟨hWc, hPW, -⟩ := (hD K ι P v a W hP hva hvP).1 hW
    have hWp : W.IsPrime := hWc.1.1
    have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
      arithVarZero K ι W ⟨hP.1, hWc.1, hh, by rw [zero_add]; exact hWc.2⟩
    obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
    choose c hc using hW.2
    set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
    have ht : IsMultiHomog t a := AvoidRing.isMultiHomog_coordProd c a
    have htW : t ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
    have ht0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => htW (hPW h)
    have h1W : (1 : MRing ι) ∉ W := fun h => hWp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    obtain ⟨N, z, hz, hNz⟩ := hPow K ι P v t a W _ (C n) 1 0 (n : FractionRing (MRing ι ⧸ P)) hPp hP.2.1.2.1 hva
      hvP hW ht htW (div_mul_cancel₀ _ ht0) (RegularityDenominator.isMultiHomog_C n) AvoidRing.isMultiHomog_one hnW h1W
      (by rw [map_one, map_one, mul_one, eq_intCast C n, map_intCast, map_intCast])
    refine ⟨n ^ N, pow_ne_zero _ hn0, ?_⟩
    have hut : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) /
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ∈ locRing P W :=
      frac_mem_locRing hPW hu ht htW (div_mul_cancel₀ _ ht0)
    rw [Int.cast_pow, hNz, ← mul_assoc, mul_div_assoc', hxv]
    exact mul_mem hut hz
  classical
  have hfin := divSupp_finite P v
  let mW : Ideal (MRing ι) → ℤ := fun W => if h : W ∈ divSupp P v then (key W h).choose else 1
  let M : ℤ := ∏ W ∈ hfin.toFinset, mW W
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W hW => by
    have hW' := hfin.mem_toFinset.mp hW
    simp only [mW, dif_pos hW']
    exact (key W hW').choose_spec.1
  refine ⟨(M : funField P), fun h => hM0 ?_, fun W hWc hPW => ⟨?_, ?_⟩⟩
  · have h' : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = 0 := by rw [h]; rfl
    have h2 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C M)) = 0 := by
      rw [eq_intCast C M, map_intCast, map_intCast]
      simp at h'
      exact h'
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
    have h3 : M ∈ P.comap (C : ℤ →+* MRing ι) := h2
    rw [hP.2.2.1] at h3
    exact Ideal.mem_bot.mp h3
  · have hc : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    exact intCast_mem (locRing P W) M
  · have hc : ((x * (M : funField P) : funField P) : FractionRing (MRing ι ⧸ P)) =
        (x : FractionRing (MRing ι ⧸ P)) * (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    by_cases hvW : v ∈ W
    · have hW : W ∈ divSupp P v := (hD K ι P v a W hP hva hvP).2 ⟨hWc, hPW, hvW⟩
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem mW (hfin.mem_toFinset.mpr hW)
      have hm := (key W hW).choose_spec.2
      rw [show M = mW W * r from hr, Int.cast_mul, ← mul_assoc]
      simp only [mW, dif_pos hW]
      exact mul_mem hm (intCast_mem _ r)
    · exact mul_mem (frac_mem_locRing hPW hu hva hvW hxv) (intCast_mem _ M)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalClosedPoints.proof (hE : regularityEmbedding_holds.Statement) (hV : VerticalEmbedding.Statement) : VerticalClosedPoints.Statement := by
  intro K _ ι _ P f g a R hP hf hg hfP hgP hR hRu
  have : P.IsPrime := hP.2.1.1
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hf hg hgP
  obtain ⟨e, he⟩ := hE K ι P R hP hR hRu
  rw [hV K ι P f g a x hP hf hg hfP hgP hx]
  have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) g :=
    ⟨a, fun _ => rfl, hg, hgP⟩
  have key : ∀ t : R, Real.log ‖e t x‖ =
      Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖) := by
    intro t
    have hg0 := eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)
    rw [← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ /
    ‖eval t (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalEmbedding.proof (hD : regularityDehomogenization_holds.Statement) (hC : regularityLocalCardinality_holds.Statement) (hL : RegularityLocalProduct.Statement) :
    VerticalEmbedding.Statement := by
  classical
  intro K _ ι _ P f g a x hP hf hg hfP hgP hx
  have : P.IsPrime := hP.2.1.1

  let t : Ideal (MRing ι) → MRing ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1
  have ht : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → IsMultiHomog (t W) a ∧ t W ∉ W := by
    intro W hWp hW
    simp only [t, dif_pos hW]
    refine ⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩
    obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp hmem
    exact (hW k).choose_spec (hWp.mem_of_pow_mem _ hk)
  have hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0 := by
    intro W hPW htW h0
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact htW (hPW h0)

  let y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P) := fun s W =>
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) /
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))
  have hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧
      ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s') := by
    intro s W hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    obtain ⟨h1, h2⟩ := ht W hW.1.1.1 hW.2
    exact ⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩

  have term : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
          (if IsHorizontal W then 0 else
            (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → HermLine ι) j).a) : ℝ) * Real.log (charOf W)) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP W hW
    have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) s :=
      ⟨a, fun _ => rfl, hs, hsP⟩
    rw [if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]
    obtain ⟨-, -, hta, htW, hy⟩ := hdata s W hW
    obtain ⟨hyW, hm⟩ := hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)
    have hy0 : y s W ≠ 0 := by
      intro h0
      have h1 := hy s
      rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact hsP h1
    rw [hm]
    exact hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0
  have hvert : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P →
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s =
        ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP
    unfold vertR
    exact finsum_mem_congr rfl fun W hW => term s hs hsP W hW
  rw [hvert f hf hfP, hvert g hg hgP]
  refine hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_
  obtain ⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by
    rcases hW with hW | hW
    · exact hdata f W hW
    · exact hdata g W hW
  exact ⟨hta, htW, hy f, hy g⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherExtra
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

def pullbackDensity_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsGoodProj (imageZ v P') Ψ →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsSectionOn (imageZ v P') A s →
    ∀ᵐ y : Fin n → ℂ, ∀ x ∈ pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ,
      logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => potOf R (L' j)) (pullQ R v Ψ) x =
        sheetDensity (imageZ v P') Ψ (pot L) (logNorm A s) y (pullW R v Ψ x)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

def PullbackDegreeCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsGoodProj (imageZ v P') Ψ →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ fibre (imageZ v P') Ψ y,
      (({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ).ncard : ℤ) =
        J (fibreIdeal κ G) 0 Fin.elim0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionHorizontal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem isHorizontal_imageZ {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (h : IsHorizontal W') :
    IsHorizontal (imageZ v W') := by
  have h' : W'.comap (C : ℤ →+* MRing ι') = ⊥ := h
  show (imageZ v W').comap (C : ℤ →+* MRing ι) = ⊥
  rw [← h']
  ext c
  simp [imageZ, Ideal.mem_comap]

theorem dim_eq {P : Ideal (MRing ι)} {d d' : ℕ} (h : IsArithVar P d) (h' : IsArithVar P d') : d = d' := by
  have e := h.2.2.2.symm.trans h'.2.2.2
  have e2 : d + Fintype.card K = d' + Fintype.card K := by exact_mod_cast e
  omega

theorem dim_add_one_le {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem isRelevant_of_le {Y Z : Ideal (MRing ι)} (hZ : IsRelevant Z) (hY : Y ≤ Z) : IsRelevant Y :=
  fun k => let ⟨i, hi⟩ := hZ k; ⟨i, fun h => hi (hY h)⟩

theorem mem_minimalPrimes {J Q : Ideal (MRing ι)} {n : ℕ} (hQ : IsArithVar Q n) (hJQ : J ≤ Q)
    (hdim : ∀ M ∈ J.minimalPrimes, IsRelevant M → IsHorizontal M → IsArithVar M n) :
    Q ∈ J.minimalPrimes := by
  have hQp : Q.IsPrime := hQ.2.1.1
  refine ⟨⟨hQp, hJQ⟩, fun q hq hqQ => ?_⟩
  have : q.IsPrime := hq.1
  obtain ⟨M, hM, hMq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hMQ : M ≤ Q := hMq.trans hqQ
  have hQh : Q.comap (C : ℤ →+* MRing ι) = ⊥ := hQ.2.2.1
  have hMh : IsHorizontal M := by
    show M.comap (C : ℤ →+* MRing ι) = ⊥
    rw [eq_bot_iff, ← hQh]
    exact Ideal.comap_mono hMQ
  have hMn := hdim M hM (isRelevant_of_le hQ.2.1.2.2 hMQ) hMh
  have : M.IsPrime := hM.1.1
  refine le_trans ?_ hMq
  by_contra hQM
  obtain ⟨x, hxQ, hxM⟩ := Set.not_subset.1 hQM
  have h := dim_add_one_le hMQ hxQ hxM
  rw [hQ.2.2.2, hMn.2.2.2] at h
  have h2 : n + Fintype.card K + 1 ≤ n + Fintype.card K := by exact_mod_cast h
  omega

omit [Fintype K] [∀ k, Fintype (ι k)] in
open Classical in

theorem sum_block (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : IsMultiHomog s α) :
    IsMultiHomog (rename v s) (Function.extend κ α 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  rw [sum_block]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then α k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hs m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

end ArithmeticIntersectionHorizontal

open ArithmeticIntersectionHorizontal in

theorem ArithmeticIntersectionHorizontal.proof (hDiv : DivSuppArithStatement) (hIm : ImageArithStatement)
    (hP0 : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement) : ArithmeticIntersectionHorizontal.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh
  classical

  let A : HermLine ι := HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) (fun k => (α k : ℤ))
  let A' : HermLine ι' :=
    HermLine.ofMetrics (fun k => maxMetric ℂ (ι' k)) (fun k => ((Function.extend κ α 0 : K' → ℕ) k : ℤ))
  have hsec : IsSectionOn (imageZ v P') A s := ⟨α, fun _ => rfl, hs, hsP⟩
  have hsec' : IsSectionOn P' A' (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, fun h => hsP (Ideal.mem_comap.mpr h)⟩
  have hW'n : IsArithVar W' n := (hDiv K' ι' P' n A' (rename v s) W' hP' hsec' hW').1 hh
  have hhQ : IsHorizontal (imageZ v W') := isHorizontal_imageZ hh
  obtain ⟨d, hdn, hQd⟩ := hIm K ι K' ι' κ v W' n hP.1 hv hW'n
  rcases hdn.lt_or_eq with hlt | heq
  ·
    right
    refine ⟨fun hm => ?_, hP0 I hI K ι K' ι' κ v W' d n L L' hv hW'n hQd hlt hL hLL'⟩
    have := dim_eq hQd ((hDiv K ι (imageZ v P') n A s _ hP hsec hm).1 hhQ)
    omega
  ·
    left
    rw [heq] at hQd
    have hle := hW'.1.1.2
    have hm : imageZ v W' ∈ divSupp (imageZ v P') s := by
      refine ⟨mem_minimalPrimes hQd ?_ fun M hM hMr hMh => (hDiv K ι (imageZ v P') n A s M hP hsec ⟨hM, hMr⟩).1 hMh,
        hQd.2.1.2.2⟩
      refine sup_le (Ideal.comap_mono (le_sup_left.trans hle)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨hm, fun G' J' hJ' => hn K ι K' ι' κ v W' G' J' L L' hv hW'n hQd hJ' hL hLL'⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalSpanTwo
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (a : Fin n → K → ℤ) (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → ¬ IsHorizontal W' →
    (imageZ v W' ∈ divSupp (imageZ v P') s ∧
        ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
          geoNum n W' (fun j => pullDeg κ (a j)) =
            J' (fibreIdeal κ G') 0 Fin.elim0 * geoNum n (imageZ v W') a) ∨
      (imageZ v W' ∉ divSupp (imageZ v P') s ∧ geoNum n W' (fun j => pullDeg κ (a j)) = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end


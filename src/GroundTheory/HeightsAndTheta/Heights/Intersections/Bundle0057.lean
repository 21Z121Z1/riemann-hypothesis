import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0052

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.AevalNeZeroOfNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ChartFiniteness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_rename_eq (G : GenFibre v P') (A : MRing ι) :
    aeval G.x' (rename v A) = algebraMap G.Φ G.Φ' (aeval G.x A) := by
  rw [aeval_rename]
  have h : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
  rw [h, MvPolynomial.aeval_algebraMap_apply]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_eq_zero_of_mem (G : GenFibre v P') {f : MRing ι'} (hf : f ∈ P') : aeval G.x' f = 0 := by
  rw [← G.genericFibre_ker_target] at hf
  exact hf

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_ne_zero_of_not_mem (G : GenFibre v P') {f : MRing ι} (hf : f ∉ imageZ v P') : aeval G.x f ≠ 0 := by
  rw [← G.ker_x] at hf
  exact hf

def coeffPoly {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F) : Polynomial F :=
  ∑ j : Fin (m + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)

theorem coeffPoly_coeff_last {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F) :
    (coeffPoly a).coeff m = a (Fin.last m) := by
  unfold coeffPoly
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro b _ hb
    have : (m : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext (by simp [h]))
    simp [this]
  · simp

end ChartFiniteness

open ChartFiniteness in

theorem ArithmeticIntersectionChartFinite.of_blockRatioAlg (hR : BlockRatioAlg.Statement) : ArithmeticIntersectionChartFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨q, rfl⟩
  apply IsAlgebraic.isIntegral
  set c : Σ k', ι' k' := ⟨q.1.1, j q.1⟩ with hc
  have hc0 : G.x' c ≠ 0 := hj q.1
  have hcP : (X c : MRing ι') ∉ P' := by
    intro h
    apply hc0
    have := aeval_eq_zero_of_mem G h
    rwa [aeval_X] at this
  obtain ⟨m, A, a, -, hAm, hmem⟩ := hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ c rfl hcP
  refine ⟨coeffPoly fun i => aeval G.x (A i), ?_, ?_⟩
  · intro h0
    have := coeffPoly_coeff_last fun i => aeval G.x (A i)
    rw [h0, Polynomial.coeff_zero] at this
    exact aeval_ne_zero_of_not_mem G hAm this.symm
  · have hsum := aeval_eq_zero_of_mem G hmem
    simp only [map_sum, map_mul, map_pow, aeval_X, aeval_rename_eq] at hsum
    have hpow : G.x' c ^ m ≠ 0 := pow_ne_zero _ hc0
    unfold coeffPoly
    simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    apply (mul_left_inj' hpow).mp
    rw [zero_mul, Finset.sum_mul, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.2
    rw [div_pow, mul_assoc, mul_assoc]
    congr 1
    have e : G.x' c ^ m = G.x' c ^ (i : ℕ) * G.x' c ^ (m - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    change G.x' _ ^ (i : ℕ) / G.x' c ^ (i : ℕ) * (G.x' c ^ (i : ℕ) * G.x' c ^ (m - i)) = _
    rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hc0)]

theorem ArithmeticIntersectionChartFinite.proof : ArithmeticIntersectionChartFinite.Statement :=
  ArithmeticIntersectionChartFinite.of_blockRatioAlg BlockRatioAlg.proof

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsNormalise
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsInAffineChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [∀ k, Fintype (ι k)] in
open Classical in

theorem exists_normalise {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} (hP' : IsMultiHomogIdeal P') {j : ∀ k : FibreBlock κ, ι' k.1}
    {z : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P')
    (hzz : SameOrbit (fun p => z' (v p)) z) (hj : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) :
    ∃ d : K' → ℂ, (∀ k, d k ≠ 0) ∧ (fun q => d q.1 * z' q) ∈ mcPts P' ∧
      (∀ p, d (v p).1 * z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, d k.1 * z' ⟨k.1, j k⟩ = 1 := by
  obtain ⟨s, hs, hzs⟩ := hzz
  let d : K' → ℂ := fun k' =>
    if h : k' ∈ Set.range κ then c h.choose / s h.choose else (z' ⟨k', j ⟨k', h⟩⟩)⁻¹
  have hdk : ∀ k, d (κ k) = c k / s k := by
    intro k
    have h : κ k ∈ Set.range κ := ⟨k, rfl⟩
    have hk : h.choose = k := hv.1 h.choose_spec
    simp only [d, dif_pos h, hk]
  have hd : ∀ k, d k ≠ 0 := by
    intro k'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := h
      rw [hdk]
      exact div_ne_zero (hc k) (hs k)
    · simp only [d, dif_neg h]
      exact inv_ne_zero (hj ⟨k', h⟩)
  refine ⟨d, hd, mcPts_smul hP' d hd hz', fun p => ?_, fun k => ?_⟩
  · have h1 : z' (v p) = s p.1 * z p := congrFun hzs p
    rw [hv.2.2.1 p, hdk, h1]
    field_simp [hs p.1]
  · have h : k.1 ∉ Set.range κ := k.2
    simp only [d, dif_neg h]
    exact inv_mul_cancel₀ (hj k)

omit [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem eq_of_normalised {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {j : ∀ k : FibreBlock κ, ι' k.1} {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    {z₁ z₂ : (Σ k', ι' k') → ℂ} (h₁v : ∀ p, z₁ (v p) = w p) (h₁j : ∀ k : FibreBlock κ, z₁ ⟨k.1, j k⟩ = 1)
    (h₂v : ∀ p, z₂ (v p) = w p) (h₂j : ∀ k : FibreBlock κ, z₂ ⟨k.1, j k⟩ = 1) (h : SameOrbit z₁ z₂) :
    z₁ = z₂ := by
  obtain ⟨t, -, ht⟩ := h
  have ht1 : ∀ k', t k' = 1 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      obtain ⟨i, hi⟩ := hw k
      have e := congrFun ht (v ⟨k, i⟩)
      simp only [h₁v, h₂v, hv.2.2.1] at e
      have e' : (t (κ k) - 1) * w ⟨k, i⟩ = 0 := by rw [sub_mul, ← e]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hi)
    · have e := congrFun ht ⟨k', j ⟨k', hk⟩⟩
      have e1 : z₁ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₁j ⟨k', hk⟩
      have e2 : z₂ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₂j ⟨k', hk⟩
      simp only [e1, e2, mul_one] at e
      exact e.symm
  rw [ht]
  funext q
  simp [ht1]

end GenericPointsInAffineChart

open GenericPointsInAffineChart PullbackDegreeCount in

theorem GenericPointsInAffineChart.proof (hFin : ArithmeticIntersectionChartFinite.Statement) (hNorm : ChartNormCount.Statement)
    (hOrb : OrbitCompNonvanish.Statement) : GenericPointsInAffineChart.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  obtain ⟨E, hE, hEw⟩ := hNorm K ι K' ι' κ v P' n G j hv hP' hP hj (hFin K ι K' ι' κ v P' n G j hv hP' hP hj)
  have hPh : IsMultiHomogIdeal (imageZ v P') := hP.2.1.2.1
  have hP'h : IsMultiHomogIdeal P' := hP'.2.1.2.1
  obtain ⟨D, a, hD, hDP, hDz⟩ := hOrb K ι (imageZ v P') E hPh hE
  refine ⟨D, a, hD, hDP, fun z hz hDz0 => ?_⟩
  obtain ⟨c, hc, hEc⟩ := hDz z hDz0
  have hw : (fun p => c p.1 * z p) ∈ mcPts (imageZ v P') := mcPts_smul hPh c hc hz
  obtain ⟨hfin, hcard, hnz⟩ := hEw _ hw hEc
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hN
  let orb : ((Σ k', ι' k') → ℂ) → Set ((Σ k', ι' k') → ℂ) := fun z' => {z'' | SameOrbit z'' z'}
  have himg : ptsOverChart P' κ v j z = orb '' N := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hzz, hjz⟩
      obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
      have hs : SameOrbit (fun q => d q.1 * z' q) z' := ⟨d, hd, rfl⟩
      refine ⟨_, ⟨hm, hdv, hdj⟩, ?_⟩
      ext y
      exact ⟨fun h => sameOrbit_comp h hs, fun h => sameOrbit_comp h (sameOrbit_flip hs)⟩
    · rintro ⟨z', ⟨hz', hzv, hzj⟩, rfl⟩
      refine ⟨z', hz', rfl, ⟨c, hc, funext hzv⟩, fun k => ?_⟩
      rw [hzj k]
      exact one_ne_zero
  have hinj : Set.InjOn orb N := by
    intro z₁ h₁ z₂ h₂ h12
    have hmem : z₁ ∈ orb z₁ := sameOrbit_self z₁
    rw [h12] at hmem
    exact eq_of_normalised hv hw.1 h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 hmem
  refine ⟨himg ▸ hfin.image orb, ?_, fun z' hz' hzz hjz q hq => ?_⟩
  · rw [himg, hinj.ncard_image, hcard]
  · obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
    have h := hnz _ hm hdv hdj q hq
    exact right_ne_zero_of_mul h

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtra
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

theorem pullbackPushforward_holds.proof (hGen : BlockGenFinite.Statement) (hIsol : FibreIsolFinite.Statement) :
    pullbackPushforward_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv hP' hP hΨ
  exact ⟨fun j => pullbackPushforward_holds.pullBad_null R hGen hv hP' hP Ψ hΨ j,
    fun y => pullbackPushforward_holds.pullFib_finite R hIsol hv hP' hP Ψ hΨ y⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PCentreOverW
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 PullbackElimination

namespace CentreOverW

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem imageZ_isRelevant {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {y : Ideal (MRing ι')} (hy : IsRelevant y) : IsRelevant (imageZ v y) := by
  intro k
  obtain ⟨i', hi'⟩ := hy (κ k)
  obtain ⟨⟨k0, i⟩, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have hk : k0 = k := hv.1 ((hv.2.2.1 ⟨k0, i⟩).symm.trans (congrArg Sigma.fst hp))
  subst hk
  refine ⟨i, fun h => hi' ?_⟩
  have h' : rename v (X ⟨k0, i⟩ : MRing ι) ∈ y := h
  rwa [rename_X, hp] at h'

theorem imageZ_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} [P'.IsPrime] {W : Ideal (MRing ι)} (hQW : imageZ v P' ≤ W)
    (R : ValuationSubring (FractionRing (MRing ι' ⧸ P')))
    (hR : ∀ a ∈ locRing (imageZ v P') W, fracMapZ v P' a ∈ R) {y : Ideal (MRing ι')}
    (hy : IsValCentre P' R y) : imageZ v y ≤ W := by
  classical
  obtain ⟨hyM, hP'y, hcen⟩ := hy
  have := hyM.1
  have := imageZ_isPrime_of_prime v P'
  intro a ha
  by_contra haW
  obtain ⟨D, hDW⟩ : ∃ D : K' → ℕ, weightedHomogeneousComponent (pullWeight v) D a ∉ W := by
    by_contra h
    push Not at h
    apply haW
    rw [← sum_weightedHomogeneousComponent (w := pullWeight v) (φ := a),
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp a)]
    exact Ideal.sum_mem _ fun D _ => h D
  set c := weightedHomogeneousComponent (pullWeight v) D a with hcdef
  have hcy : rename v c ∈ y := by
    rw [hcdef, rename_component]
    exact LocRingPow.component_mem hyM.2.1 ha D
  have hc : IsMultiHomog c (fun k => D (κ k)) :=
    isMultiHomog_of_pullWeight hv (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨u, hu, huy⟩ := exists_form_notMem (imageZ_isRelevant hv hyM.2.2) (imageZ_isPrime_of_prime v y)
    (fun k => D (κ k))
  have hcQ : c ∉ imageZ v P' := fun h => hDW (hQW h)
  have hcnz : Ideal.Quotient.mk (imageZ v P') c ∈ nonZeroDivisors (MRing ι ⧸ imageZ v P') :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hmem := hR _ (Subring.subset_closure ⟨u, c, _, hcnz, hDW, hu, hc, rfl⟩)
  rw [IsFractionRing.mk'_eq_div, map_div₀, fracMapZ_algebraMap, fracMapZ_algebraMap] at hmem
  have h2 := ((hcen _ _ _ (rename_isMultiHomog hv hc) (rename_isMultiHomog hv hu) huy).2).mp hcy
  have hne : ∀ g, g ∉ P' → algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk P' g) ≠ 0 := fun g hg => by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hc0 := hne (rename v c) (fun h => hcQ h)
  have hu0 := hne (rename v u) (fun h => huy (hP'y h))
  rw [ValuationSubring.mem_nonunits_iff] at h2
  have h3 := (R.valuation_le_one_iff _).mpr hmem
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, div_mul_div_cancel₀ hu0, div_self hc0, map_one] at h4
  exact lt_irrefl _ h4

theorem eq_or_eq_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A] {Q Y W : Ideal A}
    [Q.IsPrime] [Y.IsPrime] {s : A} (hW : W ∈ (Q ⊔ Ideal.span {s}).minimalPrimes) (hQY : Q ≤ Y) (hYW : Y ≤ W) :
    Y = Q ∨ Y = W := by
  have := hW.1.1
  have hQW : Q ≤ W := le_sup_left.trans hW.1.2
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hH := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have : (Y.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (Ideal.mk_ker.trans_le hQY)
  have : (W.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (Ideal.mk_ker.trans_le hQW)
  have : (⊥ : Ideal (A ⧸ Q)).IsPrime := Ideal.isPrime_bot
  have hb : (⊥ : Ideal (A ⧸ Q)) < Y.map (Ideal.Quotient.mk Q) := by
    refine bot_lt_iff_ne_bot.mpr fun e => h1 ?_
    rw [← Ideal.comap_map_mk hQY, e, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hYW' : Y.map (Ideal.Quotient.mk Q) < W.map (Ideal.Quotient.mk Q) := by
    refine lt_of_le_of_ne (Ideal.map_mono hYW) fun e => h2 ?_
    rw [← Ideal.comap_map_mk hQY, e, Ideal.comap_map_mk hQW]
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hb
  have e2 := (Ideal.height_add_one_le_of_lt_of_isPrime hYW').trans hH
  have e3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add (le_add_self.trans e1) le_rfl).trans e2
  exact absurd e3 (by decide)

theorem eq_of_imageZ_eq {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {n : ℕ} (hP' : IsArithVar P' (n + 1)) (hQ : IsArithVar (imageZ v P') (n + 1))
    {y : Ideal (MRing ι')} (hy : IsMultiProjPrime y) (hPy : P' ≤ y) (h : imageZ v y = imageZ v P') : y = P' := by
  classical
  have := hy.1
  by_contra hne
  obtain ⟨f, hfy, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPy (Ne.symm hne))
  obtain ⟨D, hD⟩ := LocRingPow.exists_component_not_mem hfP
  set g := weightedHomogeneousComponent (LocRingPow.multiDegWeight ι') D f
  have hgy : g ∈ y := LocRingPow.component_mem hy.2.1 hfy D
  have hg : IsMultiHomog g D :=
    LocRingPow.isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose c hc using hy.2.2
  obtain ⟨r, a, ha0, hsum⟩ := exists_elim hv hP' hQ hg hD c (fun k' h => hc k' (hPy h))
  have hT : (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ D k') ^ r ∉ y := by
    intro hm
    obtain ⟨k', -, hk⟩ := hy.1.prod_mem_iff.mp (hy.1.mem_of_pow_mem _ hm)
    exact hc k' (hy.1.mem_of_pow_mem _ hk)
  have hsum' := hPy hsum
  rw [Finset.sum_range_succ'] at hsum'
  have hrest : ∑ i ∈ Finset.range r, rename v (a (i + 1)) *
      (g ^ (i + 1) * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ D k') ^ (r - (i + 1))) ∈ y :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
      (Ideal.mul_mem_right _ _ (y.pow_mem_of_mem hgy _ (Nat.succ_pos i)))
  have h0 := (Ideal.add_mem_iff_right _ hrest).mp hsum'
  rw [pow_zero, one_mul, Nat.sub_zero] at h0
  have ha : a 0 ∈ imageZ v y := (hy.1.mem_or_mem h0).resolve_right hT
  rw [h] at ha
  exact ha0 ha

end CentreOverW

theorem CentreOverW.proof : CentreOverW.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ _ _ hW
  have := hP'.2.1.1
  intro R hR y hy
  have hQW : imageZ v P' ≤ W := le_sup_left.trans hW.1.1.2
  have hYW := CentreOverW.imageZ_le hv hQW R hR hy
  have := hy.1.1
  have := imageZ_isPrime_of_prime v P'
  have := imageZ_isPrime_of_prime v y
  rcases CentreOverW.eq_or_eq_of_mem_minimalPrimes hW.1 (Ideal.comap_mono hy.2.1) hYW with h | h
  · exact Or.inl (CentreOverW.eq_of_imageZ_eq hv hP' hQ hy.1 hy.2.1 h)
  · exact Or.inr ⟨hy.1, hy.2.1, h⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreOverFinite.proof (h : FibreIncomp.Statement) : FibreOverFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  refine (divSupp_finite P' (rename v s)).subset fun W' hW' => ?_
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    rw [← hW'.2.2] at hsW
    exact hsW
  exact ((FibreDivSupp.proof h K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW W').mp ⟨hW', hsW'⟩).1

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocIntegral.proof (h₁ : ValCentreZ.Statement) (h₂ : CentreOverW.Statement) :
    SemilocIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hP hs hsP hW
  have := hP'.2.1.1
  letI := (locToSemiloc hv P' W).toAlgebra
  let f : locRing (imageZ v P') W →+* FractionRing (MRing ι' ⧸ P') :=
    (semiLocRing P' (fibreOver v P' W)).subtype.comp (locToSemiloc hv P' W)
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := (semiLocRing P' (fibreOver v P' W)).subtype)
    Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    obtain ⟨y, hy⟩ := h₁ K' ι' P' hP'.2.1 V
    have hcase := h₂ K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW V
      (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) y hy
    have hle : semiLocRing P' (fibreOver v P' W) ≤ V.toSubring := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
      have hwy : w ∉ y := by
        rcases hcase with rfl | hy'
        · exact fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h)
        · exact hwW y hy'
      rw [SetLike.mem_coe, IsFractionRing.mk'_eq_div]
      exact (hy.2.2 a u w hu hwa hwy).1
    exact hle b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartNormPts
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ChartNormPts.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∀ z' : (Σ k', ι' k') → ℂ, (fun p => z' (v p)) ∈ mcPts (imageZ v P') →
      (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
      (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) (fun q => z' ⟨q.1.1, q.2⟩) F = 0)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end


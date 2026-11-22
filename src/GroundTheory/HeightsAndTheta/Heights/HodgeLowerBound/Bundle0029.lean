import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PVerticalGenericDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace VertFactorPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_eval_map (z : (Σ k, ι k) → ℂ) (F : MRing ι) :
    aeval z F = eval z (map (Int.castRingHom ℂ) F) := by
  rw [aeval_def, eval_map, algebraMap_int_eq]

theorem mem_mCoordIdeal_iff_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {F : MRing ι}
    {d : K → ℕ} (hF : IsMultiHomog F d) : F ∈ mCoordIdeal y ↔ aeval y F = 0 := by
  refine ⟨fun h => ?_, mem_mCoordIdeal_of_aeval_eq_zero y hF⟩
  have h' : mConeMap y F = 0 := RingHom.mem_ker.mp h
  rw [mConeMap_of_isMultiHomog y hF] at h'
  have hm : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  exact C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hm)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem X_mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (q : Σ k, ι k) :
    (X q : MRing ι) ∈ mCoordIdeal y ↔ y q = 0 := by
  show X q ∈ RingHom.ker (mConeMap y) ↔ _
  rw [RingHom.mem_ker]
  simp [mConeMap, X_ne_zero]

theorem mCoordIdeal_le {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : mCoordIdeal y ≤ mCoordIdeal z := by
  classical
  intro F hF
  show F ∈ RingHom.ker (mConeMap z)
  rw [RingHom.mem_ker]
  ext m
  rw [coeff_zero, ← Finsupp.equivFunOnFinite_symm_coe m,
    HilbertSamuel.GenFibreHomog.coeff_mConeMap, aeval_eq_eval_map]
  exact hz.2 _ (HilbertSamuel.GenFibreHomog.isMultiHomogIdeal_mCoordIdeal y F hF _)

theorem prod_X_pow_add (d d' : K → ℕ) {R : Type} [CommRing R] :
    (∏ k, (X k : MvPolynomial K R) ^ (d + d') k) =
      (∏ k, (X k : MvPolynomial K R) ^ d k) * ∏ k, (X k : MvPolynomial K R) ^ d' k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

theorem prod_X_pow_eq_monomial (d : K → ℕ) {R : Type} [CommRing R] :
    (∏ k, (X k : MvPolynomial K R) ^ d k) = monomial (Finsupp.equivFunOnFinite.symm d) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp

theorem isMultiHomog_chartForm [DecidableEq K] (c : (k : K) → ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  apply HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
  have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k)
    (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (NumbersDVR.blockWeight ι) ⟨k, c k⟩).pow (d k))
  convert this using 1
  funext k
  simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]

theorem exists_value {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (hV : IsVerticalDivisorAt (mCoordIdeal y) p b f g) (c : (k : K) → ι k)
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    ∃ v, v ≠ 0 ∧ IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z v := by
  classical
  have hPW : mCoordIdeal y ≤ mCoordIdeal z := mCoordIdeal_le hz
  have hWp : (mCoordIdeal z).IsPrime := RingHom.ker_isPrime _
  have hrel : IsRelevant (mCoordIdeal z) := fun k =>
    ⟨c k, fun h => hc k ((X_mem_mCoordIdeal_iff z _).1 h)⟩
  have hpW : (C (p : ℤ) : MRing ι) ∉ mCoordIdeal z := by
    intro h
    have h' : mConeMap z (C (p : ℤ)) = 0 := RingHom.mem_ker.mp h
    simp [mConeMap, hp] at h'
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre _ hWp hPW hrel hpW
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfy : aeval y f ≠ 0 := fun h => hV.num_not_mem ((mem_mCoordIdeal_iff_of_homog y hf).2 h)
  have hgy : aeval y g ≠ 0 := fun h => hV.den_not_mem ((mem_mCoordIdeal_iff_of_homog y hg).2 h)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc k ((X_mem_mCoordIdeal_iff z _).1 (hPW ((X_mem_mCoordIdeal_iff y _).2 h)))

  have hu' : mConeMap z u ≠ 0 := fun h => hu (RingHom.mem_ker.mpr h)
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hu'
  set e : K → ℕ := ⇑m with he
  set ue := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e u with hue_def
  have hue : IsMultiHomog ue e := HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
    (weightedHomogeneousComponent_isWeightedHomogeneous e u)
  have huez : aeval z ue ≠ 0 := by
    rw [← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap] at hm
    exact hm
  have hueW : ue ∉ mCoordIdeal z := fun h => huez ((mem_mCoordIdeal_iff_of_homog z hue).1 h)
  have huey : aeval y ue ≠ 0 := fun h => hueW (hPW ((mem_mCoordIdeal_iff_of_homog y hue).2 h))

  have hrel' : mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k) =
      mConeMap y v * (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) := by
    have h : mConeMap y (u * f - v * g) = 0 := RingHom.mem_ker.mp huv
    rw [map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y hf,
      mConeMap_of_isMultiHomog y hg] at h
    exact h

  have hcoef := congrArg (coeff (m + Finsupp.equivFunOnFinite.symm bf)) hrel'
  rw [prod_X_pow_eq_monomial, prod_X_pow_eq_monomial, C_mul_monomial, C_mul_monomial,
    coeff_mul_monomial', coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one,
    mul_one] at hcoef
  have hcu : coeff m (mConeMap y u) = aeval y ue := by
    rw [← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap]
  rw [hcu] at hcoef
  by_cases hle : Finsupp.equivFunOnFinite.symm bg ≤ m + Finsupp.equivFunOnFinite.symm bf
  swap
  · rw [if_neg hle] at hcoef
    exact absurd hcoef (mul_ne_zero huey hfy)
  rw [if_pos hle] at hcoef
  set d' : K → ℕ := ⇑(m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg) with hd'
  set a := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) d' v with ha_def
  have ha : IsMultiHomog a d' := HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
    (weightedHomogeneousComponent_isWeightedHomogeneous d' v)
  have hcv : coeff (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg)
      (mConeMap y v) = aeval y a := by
    rw [← Finsupp.equivFunOnFinite_symm_coe
      (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg),
      HilbertSamuel.GenFibreHomog.coeff_mConeMap]
  rw [hcv] at hcoef

  have hdeg : d' + bg = e + bf := by
    have := congrArg (⇑) (tsub_add_cancel_of_le hle)
    simpa [hd', he, Finsupp.coe_add] using this

  have hkey : a * u - ue * v ∈ mCoordIdeal y := by
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y ha,
      mConeMap_of_isMultiHomog y hue]
    have hG : (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) ≠ 0 :=
      mul_ne_zero (C_ne_zero.2 hgy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
    refine mul_right_cancel₀ hG ?_
    calc C (aeval y a) * (∏ k, (X k : MvPolynomial K Ω) ^ d' k) * mConeMap y u *
          (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k)
        = C (aeval y a * aeval y g) * (∏ k, (X k : MvPolynomial K Ω) ^ (d' + bg) k) *
            mConeMap y u := by rw [prod_X_pow_add, map_mul]; ring
      _ = C (aeval y ue * aeval y f) * (∏ k, (X k : MvPolynomial K Ω) ^ (e + bf) k) *
            mConeMap y u := by rw [hcoef, hdeg]
      _ = C (aeval y ue) * (∏ k, (X k : MvPolynomial K Ω) ^ e k) *
            (mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k)) := by
          rw [prod_X_pow_add, map_mul]; ring
      _ = _ := by rw [hrel']; ring
  have haW : a ∉ mCoordIdeal z := by
    intro h
    have h2 : ue * v ∈ mCoordIdeal z := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right u _ h) (hPW hkey)
      simpa using this
    rcases hWp.mem_or_mem h2 with h3 | h3
    · exact hueW h3
    · exact hv h3
  have haz : aeval z a ≠ 0 := fun h => haW ((mem_mCoordIdeal_iff_of_homog z ha).2 h)

  have hMz : ∀ d : K → ℕ, eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) =
      ∏ k, z ⟨k, c k⟩ ^ d k := fun d => by simp [map_prod]
  have hMy : ∀ d : K → ℕ, aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) = ∏ k, y ⟨k, c k⟩ ^ d k :=
    fun d => by simp [map_prod]
  have hMz0 : ∀ d : K → ℕ, (∏ k, z ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hMy0 : ∀ d : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hchart : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hb, Pi.neg_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k)]
    congr 1
    ring
  refine ⟨eval z (map (Int.castRingHom ℂ) (a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k)) /
    eval z (map (Int.castRingHom ℂ) (ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k)), ?_,
    e + bf, a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k, ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [map_mul]
    rw [hMz, hMz, ← aeval_eq_eval_map, ← aeval_eq_eval_map]
    exact div_ne_zero (mul_ne_zero haz (hMz0 _)) (mul_ne_zero huez (hMz0 _))
  · rw [← hdeg]
    exact LowerBoundFree.isMultiHomog_mul ha (isMultiHomog_chartForm c bg)
  · exact LowerBoundFree.isMultiHomog_mul hue (isMultiHomog_chartForm c bf)
  · rw [map_mul, hMy]
    exact mul_ne_zero huey (hMy0 _)
  · rw [map_mul, map_mul, hMy, hMy, ← hchart]
    field_simp
    linear_combination (-(chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k)) * hcoef
  · simp only [map_mul]
    rw [hMz, ← aeval_eq_eval_map]
    exact mul_ne_zero huez (hMz0 _)

end VertFactorPos

open VertFactorPos in

theorem VertFactorPos.proof : VertFactorPos.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p hp z hz
  have hex : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0 :=
    ⟨fun k => (hz.1 k).choose, fun k => (hz.1 k).choose_spec⟩
  rw [ComponentData.vertFactor, dif_pos hex]
  obtain ⟨v, hv0, hv⟩ := exists_value hz (D.S_prime p hp).ne_zero (D.vertical p hp) hex.choose
    hex.choose_spec
  rw [valAt_eq hz hv]
  exact mul_pos (norm_pos_iff.2 hv0) (norm_pos_iff.2
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hex.choose_spec k)))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVerticalTwistGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalTwistGenDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem intNum_snoc_eq_zero {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n p : ℕ} {b : K → ℤ} {f g : MRing ι}
    (hP : IsArithVar P (n + 1 + 1)) (hp : p.Prime) (hV : IsVerticalDivisorAt P p b f g)
    (L : Fin n → K → ℤ) :
    NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
      (Fin.snoc (α := fun _ => K → ℤ) L b) = 0 := by
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  have hPN : NumbersDVR.IsMultiProjPrime P := (Bridge.isMultiProjPrime_iff P).mpr hP.2.1
  have : P.IsPrime := hPN.isPrime
  have hPh : IsHorizontal P := hP.2.2.1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpP : (C (p : ℤ) : MRing ι) ∉ P := by
    intro h
    have h0 : (p : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hPh, Ideal.mem_bot] at h0
    exact hp0 h0
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfN : NumbersDVR.IsMultiHomog f bf := (Bridge.isMultiHomog_iff f bf).mpr hf
  have hgN : NumbersDVR.IsMultiHomog g bg := (Bridge.isMultiHomog_iff g bg).mpr hg

  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre P ‹_› le_rfl hP.2.1.2.2 hpP
  obtain ⟨u', v', e, e', hu', hv', hdeg, hu'P, hv'P, huv'⟩ :=
    NumbersDVR.exists_form_pair hPN.multiHomog le_rfl hfN hgN hV.num_not_mem hV.den_not_mem hu hv huv

  have hkey : ∀ W' : Ideal (MRingOver ℚ ι), W'.IsPrime → P.map φ ≤ W' → NumbersDVR.IsRelevant W' →
      NumbersDVR.divCycle (P.map φ) (φ v') W' = NumbersDVR.divCycle (P.map φ) (φ u') W' := by
    intro W' hW' hle hrel
    have hPle : P ≤ W'.comap φ := fun x hx => hle (Ideal.mem_map_of_mem φ hx)
    have hrel' : IsRelevant (W'.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have h' : φ (X ⟨k, i⟩) ∈ W' := h
      rwa [hφ, map_X] at h'
    have hpW' : (C (p : ℤ) : MRing ι) ∉ W'.comap φ := by
      intro h
      have hu : IsUnit (φ (C (p : ℤ))) := by
        rw [hφ, map_C]
        exact (isUnit_iff_ne_zero.mpr (by simpa using hp0)).map C
      exact hW'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    obtain ⟨s, t, hs, ht, hst⟩ := hV.unit_off_fibre _ (Ideal.comap_isPrime φ W') hPle hrel' hpW'
    have h1 : g * (s * v' - t * u') ∈ P := by
      have e1 : g * (s * v' - t * u') = u' * (s * f - t * g) - s * (u' * f - v' * g) := by ring
      rw [e1]
      exact P.sub_mem (P.mul_mem_left _ hst) (P.mul_mem_left _ huv')
    have h2 : s * v' - t * u' ∈ P := (‹P.IsPrime›.mem_or_mem h1).resolve_left hV.den_not_mem
    have h3 : φ s * φ v' - φ t * φ u' ∈ P.map φ := by
      rw [← map_mul, ← map_mul, ← map_sub]
      exact Ideal.mem_map_of_mem φ h2
    have hs' : φ s ∉ W' := hs
    have ht' : φ t ∉ W' := ht
    exact NumbersDVR.divCycle_eq_of_mul_sub_mem hs' ht' h3
  have hrat : NumbersDVR.ratDiv (P.map φ) (φ v') (φ u') = 0 := by
    funext W'
    show NumbersDVR.divCycle _ _ W' - NumbersDVR.divCycle _ _ W' = 0
    by_cases h1 : NumbersDVR.divCycle (P.map φ) (φ v') W' = 0
    · by_cases h2 : NumbersDVR.divCycle (P.map φ) (φ u') W' = 0
      · rw [h1, h2, sub_zero]
      · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h2
        rw [hkey W' a1 a2 a3, sub_self]
    · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h1
      rw [hkey W' a1 a2 a3, sub_self]

  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hv'Q : φ v' ∉ P.map φ := fun h => hv'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh v').mp h)
  have hu'Q : φ u' ∉ P.map φ := fun h => hu'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh u').mp h)
  have hab : ∀ k, (e' k : ℤ) - e k = b k := by
    intro k
    have h1 : (e' k : ℤ) + bg k = e k + bf k := by exact_mod_cast congrFun hdeg k
    have h2 : (bf k : ℤ) - bg k = b k := congrFun hb k
    rw [← h2]
    linarith
  have hR := NumbersDVR.IntNumRatSection.proof FieldNumbers.CutRational.full ℚ K ι n (P.map φ) hXN hX.2
    L b (φ v') (φ u') e' e (NineStatements.VerticalGenericDeg.isMultiHomog_map hv')
    (NineStatements.VerticalGenericDeg.isMultiHomog_map hu') hv'Q hu'Q hab
  rw [hrat] at hR
  rw [hR]
  simp [NumbersDVR.cycEval]

end VerticalTwistGenDeg

theorem VerticalTwistGenDeg.proof : VerticalTwistGenDeg.Statement := by
  intro K _ ι _ P d a s b f g hP hs
  classical
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  obtain _ | n := d
  · unfold genDeg
    congr 1
    funext i
    exact i.elim0
  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map φ) = (n + 1 : ℕ) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set F := intNumMultilinear (P.map φ) (n + 1) hXN.multiHomog hXN.relevant hd with hF

  have hposition : ∀ p ∈ s, ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = b p → F bs = 0 := by
    intro p hps bs i hi
    obtain ⟨hp, hV⟩ := hs p hps
    have h := FieldNumbers.IntNumSymm.full ℚ K ι (P.map φ) (n + 1) bs (Equiv.swap i (Fin.last n))
    rw [hF, intNumMultilinear_apply, ← h]
    have e1 : bs ∘ Equiv.swap i (Fin.last n) = Fin.snoc (α := fun _ => K → ℤ)
        (fun j => bs (Equiv.swap i (Fin.last n) (Fin.castSucc j))) (b p) := by
      funext j
      induction j using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [e1]
    exact VerticalTwistGenDeg.intNum_snoc_eq_zero hP hp hV _

  have hB : ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = ∑ p ∈ s, b p → F bs = 0 := by
    intro bs i hi
    have e2 : bs = Function.update bs i (∑ p ∈ s, b p) := by rw [← hi, Function.update_eq_self]
    rw [e2, ← MultilinearMap.toLinearMap_apply, map_sum]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [MultilinearMap.toLinearMap_apply]
    exact hposition p hp _ i (Function.update_self _ _ _)
  have hg : ∀ c, genDeg P (n + 1) c = F (fun _ => c) := fun c => by
    rw [hF, intNumMultilinear_apply, genDeg]
  rw [hg, hg, show (fun _ : Fin (n + 1) => a + ∑ p ∈ s, b p) =
    (fun _ => a) + (fun _ => ∑ p ∈ s, b p) from rfl, F.map_add_univ,
    Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ]
  · intro S _ hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra h
      exact hS (Finset.eq_univ_iff_forall.2 fun i => not_not.1 (not_exists.1 h i))
    exact hB _ i (by simp [Finset.piecewise, hi])
  · intro h
    exact absurd (Finset.mem_univ _) h

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryPtsNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDivisorPreimageNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def DivisorPreimageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (M : CxModel P d) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas),
    IsPtsNull P d {z | M.proj z ∉ R.Yo}

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelLogIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ModelLogIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (L : HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (u : M.Xc → ℝ) (C C' : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N → @Measurable M.Xc ℝ (borel M.Xc) _ u →
    (∀ x ∈ R.Yo, |u x| ≤ C + C' * Real.log (R.r x)) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ R.Yo → g z = u (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomCuspIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuHomCuspIntegrable.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    IsPtsIntegrable (mCoordIdeal D.y) (fun (_ : Fin D.n) => phMu X.H) X.Cd.cuspWeight

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomDensityNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuHomDensityNonneg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ)),
    IsGoodProj (mCoordIdeal D.y) Q →
      ∀ᵐ y : Fin D.n → ℂ, ∀ w,
        0 ≤ sheetDensity (mCoordIdeal D.y) Q (fun (_ : Fin D.n) => phMu X.H) (fun _ => 1) y w

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomMassIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def MuHomMassIntegrable.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    IsPtsIntegrable (mCoordIdeal D.y) (fun (_ : Fin D.n) => phMu X.H) (fun _ => 1)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end


import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain WithZero

noncomputable section

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

theorem exists_C_mul_eq_C_pow_mul {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by
  have hlt : v.intValuation a < 1 := by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := (v.intValuation_lt_one_iff_dvd a).mp hlt
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hle
    have h2 : v.asIdeal ^ 2 ∣ Ideal.span {a} := ⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩
    have h3 := (v.intValuation_le_pow_iff_dvd a 2).mpr h2
    rw [ha, exp_le_exp] at h3
    norm_num at h3
  have hJj : ¬ J ^ j ≤ v.asIdeal := fun h => hJv (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJj
  have hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j} := by
    rw [← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]
  have hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)} := by
    have h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) *
        Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp
    rw [← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨t, htv, h, by rw [← hh, mul_comm]⟩

end Dedekind

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_map_of_coeff_notMem (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v)
      (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding,
      (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem adicAbv_of_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha,
    WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  have h1 : Multiplicative.toAdd (unzero (exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [h1, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]

theorem irreducible_algebraMap_C (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing (ParDVR e n v)] {a : 𝓞 K} (ha : v.intValuation a = exp (-1 : ℤ)) :
    Irreducible (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  have hnu : ¬ IsUnit (φ (C a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    exact fun h => h (Ideal.mem_map_of_mem _ hav)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ParDVR e n v)
  obtain ⟨x, s, rfl⟩ : ∃ (x : MvPolynomial (Par e n) (𝓞 K)) (s : (parPrime e n v).primeCompl),
      IsLocalization.mk' (ParDVR e n v) x s = ϖ := by
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl ϖ
    exact ⟨x, s, hxs⟩
  have hx : x ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ 1) := by
    rw [pow_one]
    by_contra hx
    exact hϖ.not_isUnit
      ((IsLocalization.AtPrime.isUnit_mk'_iff (ParDVR e n v) (parPrime e n v) x s).mpr hx)
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha 1 hx
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hx2 : φ x = φ (C a) * (↑htu.unit⁻¹ * φ h) := by
    have h2 := congrArg φ hth
    rw [map_mul, map_mul, pow_one] at h2
    calc φ x = ↑htu.unit⁻¹ * (φ (C t) * φ x) := by
          rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = φ (C a) * (↑htu.unit⁻¹ * φ h) := by rw [h2]; ring
  have hϖ' : IsLocalization.mk' (ParDVR e n v) x s =
      φ (C a) * (↑htu.unit⁻¹ * φ h * IsLocalization.mk' (ParDVR e n v) 1 s) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hx2]
    ring
  rw [hϖ'] at hϖ
  rcases hϖ.isUnit_or_isUnit rfl with hu | hu
  · exact (hnu hu).elim
  · exact (irreducible_mul_isUnit hu).mp hϖ

end NumberField

theorem GaussDVR.proof (h1 : ParDVRIsDVR.Statement) : GaussDVR.Statement := by
  intro K _ _ e n v g hg
  have := h1 K e n v
  classical
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  let μ : 𝓞 K → ℕ := fun b => multiplicity v.asIdeal (Ideal.span {b})
  have hval : ∀ b : 𝓞 K, b ≠ 0 → ∀ k : ℕ, b ∈ v.asIdeal ^ k ↔ k ≤ μ b := by
    intro b hb k
    rw [← v.intValuation_le_pow_iff_mem, v.intValuation_eq_exp_neg_multiplicity hb, exp_le_exp]
    simp only [μ]
    omega
  have hne : g.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hg)
  obtain ⟨d0, hd0, hmin⟩ := g.support.exists_mem_eq_inf' hne (fun d => μ (g.coeff d))
  set m := g.support.inf' hne (fun d => μ (g.coeff d)) with hm
  have hgm : g ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ m) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    by_cases hd : g.coeff d = 0
    · rw [hd]
      exact Ideal.zero_mem _
    · exact (hval _ hd m).mpr (Finset.inf'_le _ (mem_support_iff.mpr hd))
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha m hgm
  have hb0 : g.coeff d0 ≠ 0 := mem_support_iff.mp hd0
  have hh : h.coeff d0 ∉ v.asIdeal := by
    intro hmem
    have hc := congrArg (coeff d0) hth
    rw [coeff_C_mul, ← C_pow, coeff_C_mul] at hc
    have h3 : t * g.coeff d0 ∈ v.asIdeal ^ (m + 1) := by
      rw [hc, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hav m) hmem
    have h4 := (v.intValuation_le_pow_iff_mem _ _).mpr h3
    rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht, one_mul, v.intValuation_le_pow_iff_mem,
      hval _ hb0] at h4
    omega
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hhu : IsUnit (φ h) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro hP
    exact hh ((MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp hP d0)
  have hord : Ring.ord (ParDVR e n v) (φ g) = m := by
    rw [Ring.ord_eq_addVal]
    have h0 := congrArg φ hth
    rw [map_mul φ, map_mul φ, map_pow φ] at h0
    have h2 := congrArg (IsDiscreteValuationRing.addVal (ParDVR e n v)) h0
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer (irreducible_algebraMap_C e n v ha),
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr htu,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hhu] at h2
    simpa using h2
  have hK0 := congrArg (MvPolynomial.map (algebraMap (𝓞 K) K)) hth
  rw [map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)),
    map_pow (MvPolynomial.map (algebraMap (𝓞 K) K)), MvPolynomial.map_C, MvPolynomial.map_C] at hK0
  have hK := congrArg (gaussNorm v) hK0
  rw [← C_pow, gaussNorm_C_mul, gaussNorm_C_mul, map_pow,
    adicAbv_of_intValuation_eq v ha, gaussNorm_map_of_coeff_notMem v h ⟨d0, hh⟩, ← FinitePlace.norm_embedding,
    (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr ht, one_mul, mul_one] at hK
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  rw [hord, ENat.toNat_natCast, hK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hN)]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.POrdEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem specComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : (specComps I v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1

theorem vertComps_finite' {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1

open Classical in

theorem OrdEq.proof (hni : NormIdentity.Statement) (hnl : NormLength.Statement)
    (hld : LengthDecomp.Statement) (hmax : SpecMax.Statement) (hlen : SpecLength.Statement)
    (hres : SpecResidue.Statement) (hvs : VertSpec.Statement) (hinj : SecBLinInj.Statement)
    (hfin : SecBFinite.Statement) (htf : SecBTorsionFree.Statement) (hdvr : ParDVRIsDVR.Statement) :
    OrdEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  set f := g.map (algebraMap (𝓞 K) K)
  set ℓ := secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))
  obtain ⟨w, hw⟩ := hni K n e I g u v hI hf hu hprim
  rw [hw, Ring.ord_mul_of_isUnit_left w.isUnit]
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I f v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  have hℓ : Function.Injective fun b : SecB e I v => ℓ * b := hinj K n e I f u v hI hf hu
  rw [hnl _ _ ℓ hℓ]

  have hN0 : Algebra.norm (ParDVR e n v) ℓ ≠ 0 := by
    rw [Algebra.norm_apply, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hℓ
  have hfinite : Module.length (ParDVR e n v) (SecB e I v ⧸ Ideal.span {ℓ}) ≠ ⊤ := by
    rw [← hnl _ _ ℓ hℓ]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hN0)
  rw [hld _ _ ℓ hfinite]

  obtain ⟨hmax1, hmax2⟩ := hmax K n e I f v hI hf
  choose W hW hWu using fun 𝔫 : MaximalSpectrum (SecB e I v) => hmax2 𝔫.asIdeal 𝔫.isMaximal
  set G : Ideal (MvPolynomial (Fin n) (𝓞 K)) → ℕ∞ := fun W =>
    (if linForm u ∈ W then (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0) *
      (chowDegree (reduceMod v W) (e + 1) : ℕ∞) with hG
  have hbij : Set.BijOn W Set.univ (specComps I v) := by
    refine ⟨fun 𝔫 _ => (hW 𝔫).1, fun 𝔫₁ _ 𝔫₂ _ h => ?_, fun W' hW' => ?_⟩
    · apply MaximalSpectrum.ext
      rw [← (hW 𝔫₁).2, ← (hW 𝔫₂).2, h]
    · refine ⟨⟨secIdealOf e I v W', hmax1 W' hW'⟩, Set.mem_univ _, ?_⟩
      exact (hWu _ W' ⟨hW', rfl⟩).symm
  rw [← finsum_mem_univ, finsum_mem_eq_of_bijOn W hbij (g := G) fun 𝔫 _ => by
    rw [hlen K n e I f u v hI hf hu 𝔫 (W 𝔫) (hW 𝔫).1 (hW 𝔫).2, ← (hW 𝔫).2,
      hres K n e I f v hI hf (W 𝔫) (hW 𝔫).1]]

  have hs := specComps_finite I v
  have hv := vertComps_finite' I u v
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, vertDeg, Nat.cast_finsum_mem hv,
    finsum_mem_eq_finite_toFinset_sum _ hv]
  have hset : hv.toFinset = hs.toFinset.filter fun W => linForm u ∈ W := by
    ext W
    simp [hvs K n e I f u v hI hf hu]
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [hG]
  split_ifs <;> simp

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem eval_parYF_comp (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C,
      eval₂Hom_C]
    rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  · simp [parYF]

theorem ParAlgIndep.proof : ParAlgIndep.Statement := by
  intro K _ _ e n
  let _ := (kToFrac K e n).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))
  let M : Submonoid (MvPolynomial (Par e n) (𝓞 K)) := (nonZeroDivisors (𝓞 K)).map C
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s
  have hc := eval_parYF_comp K e n
  have ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0 := by
    rw [← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]
  have ha0 : a = 0 := IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)
  subst ha0
  exact IsLocalization.mk'_zero _

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain IsLocalRing

noncomputable section

theorem ParDVRIsDVR.proof : ParDVRIsDVR.Statement := by
  intro K _ _ e n v
  let A := MvPolynomial (Par e n) (𝓞 K)
  let R := ParDVR e n v
  let Rv := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance

  have hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v := by
    intro s hs h
    rw [parPrime, MvPolynomial.mem_map_C_iff] at h
    exact hs (by simpa using h 0)
  have hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]
  let φ : Rv →+* R := IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R)
    fun s => by
      rw [hOR, RingHom.comp_apply]
      exact IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)
  have hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R := IsLocalization.lift_comp _
  have hmax : maximalIdeal R = (maximalIdeal Rv).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rv
  have hspan : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]

  have hne : maximalIdeal R ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)
    rw [hbot, Ideal.mem_bot, hOR, RingHom.comp_apply] at hmem
    have hinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))
    exact hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))
  have hnf : ¬IsField R := fun h => hne (isField_iff_maximalIdeal_eq.mp h)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 4 0).mp
    (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

theorem PrimitiveScale.proof : PrimitiveScale.Statement := by
  intro K _ _ v σ f hf
  classical
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanFinset (𝓞 K) f.support (fun m => f.coeff m)
    with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, FractionalIdeal.spanFinset_ne_zero]
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
    exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hm⟩
  have hJJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ
  have hcoeff : ∀ m, f.coeff m ∈ J := by
    intro m
    by_cases hm : f.coeff m = 0
    · rw [hm, ← FractionalIdeal.mem_coe]; exact Submodule.zero_mem _
    · rw [← FractionalIdeal.mem_coe, hJdef, FractionalIdeal.spanFinset_coe]
      exact Submodule.subset_span ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
  have hint : ∀ c ∈ J⁻¹, ∀ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m := by
    intro c hc m
    have h1 : f.coeff m * c ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul (hcoeff m) hc
    rw [hJJ, FractionalIdeal.mem_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [hy, mul_comm]⟩

  have hex : ∃ c ∈ J⁻¹, ∃ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m ∧ y ∉ v.asIdeal := by
    by_contra hne
    push Not at hne
    let S : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) v.asIdeal
    have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ S := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro j hj c hc
      have hJS : (J : Submodule (𝓞 K) K) ≤ S.comap (LinearMap.mulRight (𝓞 K) c) := by
        rw [hJdef, FractionalIdeal.spanFinset_coe, Submodule.span_le]
        rintro _ ⟨m, -, rfl⟩
        obtain ⟨y, hy⟩ := hint c hc m
        refine Submodule.mem_map.mpr ⟨y, hne c hc m y hy, ?_⟩
        simp only [Algebra.linearMap_apply, LinearMap.mulRight_apply]
        rw [hy, mul_comm]
      exact hJS hj
    have h1 : (1 : K) ∈ S := by
      apply hle
      rw [hJJ, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    obtain ⟨y, hy, hy1⟩ := Submodule.mem_map.mp h1
    have : y = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      simpa using hy1
    rw [this] at hy
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hy)
  obtain ⟨c, hc, m0, y0, hy0, hy0v⟩ := hex
  have hcoeffs : ((C c * f).coeffs : Set K) ⊆ Set.range (algebraMap (𝓞 K) K) := by
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    obtain ⟨y, hy⟩ := hint c hc m
    exact ⟨y, by rw [hy, MvPolynomial.coeff_C_mul]⟩
  obtain ⟨g, hg⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeffs
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0v
    have : algebraMap (𝓞 K) K y0 = 0 := by rw [hy0, zero_mul]
    rw [(IsFractionRing.injective (𝓞 K) K).eq_iff.mp (this.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨c, g, hc0, hg, m0, ?_⟩
  have hgm : algebraMap (𝓞 K) K (g.coeff m0) = algebraMap (𝓞 K) K y0 := by
    rw [hy0, ← MvPolynomial.coeff_map, hg, MvPolynomial.coeff_C_mul]
  rwa [(IsFractionRing.injective (𝓞 K) K) hgm]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def SpecChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (𝔫 : MaximalSpectrum (SecB e I v)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) [W.IsPrime],
        W ∈ specComps I v → secIdealOf e I v W = 𝔫.asIdeal →
          ∃ ψ : Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)) →+*
              Localization.AtPrime 𝔫.asIdeal,
            (∀ g : MvPolynomial (Fin n) (𝓞 K),
              ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
                algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
                  (Ideal.Quotient.mk _ (g.map (algebraMap (𝓞 K) (ParDVR e n v))))) ∧
            IsLocalHom (ψ.comp (Ideal.Quotient.mk _)) ∧
            @RingHom.Flat (Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
              (Localization.AtPrime 𝔫.asIdeal) _ _ ψ ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal)

end

end GroundTheory.Heights₂.Heights.Vertical
end


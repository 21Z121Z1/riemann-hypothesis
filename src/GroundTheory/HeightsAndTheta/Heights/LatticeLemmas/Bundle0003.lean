import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHeightOfCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

namespace HeightOfCycle

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_eq_iSup {ι : Type*} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {f : MvPolynomial ι K} (hf : f ≠ 0) (S : Finset (ι →₀ ℕ)) (hS : f.support ⊆ S) :
    gaussNorm v f = ⨆ m : S, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) := by
  have e : ∀ m, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) =
      NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m) := fun m ↦ by
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  simp_rw [e]
  obtain ⟨m, hm, hmax⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
  have : Nonempty S := ⟨⟨m, hS hm⟩⟩
  apply le_antisymm
  · rw [gaussNorm_eq_gaussNormOf, hmax]
    exact le_ciSup (f := fun m : S ↦ NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m))
      (Set.finite_range _).bddAbove ⟨m, hS hm⟩
  · exact ciSup_le fun m ↦ le_gaussNormOf _ f m

theorem finsum_log_gaussNorm_map {E : Type*} [Field E] [NumberField E] [Algebra E K] {ι : Type*}
    {P : MvPolynomial ι E} (hP : P ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (P.map (algebraMap E K))) =
      Module.finrank E K *
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) := by
  have hPK : P.map (algebraMap E K) ≠ 0 :=
    fun h0 ↦ hP (MvPolynomial.map_injective _ (algebraMap E K).injective (by rw [h0, _root_.map_zero]))
  obtain ⟨m0, hm0⟩ := support_nonempty.mpr hP
  have hy : (fun m : P.support ↦ P.coeff m) ≠ 0 :=
    Function.ne_iff.mpr ⟨⟨m0, hm0⟩, mem_support_iff.mp hm0⟩
  have eK : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      gaussNorm v (P.map (algebraMap E K)) =
        ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (algebraMap E K (P.coeff m)) :=
    fun v ↦ by
      rw [gaussNorm_eq_iSup v hPK P.support (support_map_subset _ _)]
      simp_rw [coeff_map]
  have eE : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      gaussNorm v P = ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (P.coeff m) :=
    fun v ↦ gaussNorm_eq_iSup v hP P.support subset_rfl
  simp_rw [eK, eE]
  rw [finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace K ↦ Real.log (⨆ m : P.support, w (algebraMap E K (P.coeff m)))),
    finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace E ↦ Real.log (⨆ m : P.support, w (P.coeff m)))]
  exact finsum_log_iSup_algebraMap hy

theorem finsum_log_gaussNorm_prod {ι α : Type*} (s : Finset α) (L : α → MvPolynomial ι K)
    (hL : ∀ q, L q ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (∏ q ∈ s, L q)) =
      ∑ q ∈ s, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (L q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]
    simp_rw [gaussNorm_C, map_one, Real.log_one, finsum_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, finsum_log_gaussNorm_mul (hL a)
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q), ih, Finset.sum_insert ha]

end HeightOfCycle

open HeightOfCycle in

theorem HeightOfCycle.proof (h1 : HeightOfPoint.Statement) (h2 : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement := by
  intro F _ _ W _ _ _ _ h n w hw E _ _ _ K _ _ _ _ _ m yv hyv c hc P hP

  have hL : ∀ q, (∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 := by
    intro q h0
    apply hyv q
    have hle : Submodule.span (𝓞 F) (Set.range w) ≤ LinearMap.ker (yv q) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrArg (coeff (Finsupp.single k 1)) h0
      simp only [coeff_sum, coeff_C_mul, coeff_X, coeff_zero] at this
      rw [Finset.sum_eq_single k (fun j _ hj ↦ by
        rw [if_neg (fun e ↦ hj (Finsupp.single_left_injective one_ne_zero e)), mul_zero])
        (by simp)] at this
      simpa using this
    rw [hw, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hle
  have hprod : (∏ q, ∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q
  have hPne : P ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hP
    exact mul_ne_zero (C_ne_zero.mpr hc) hprod hP.symm
  have hr : (Module.finrank E K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

  have hpt : ∀ q, pointHeight h (yv q) = (Module.finrank ℚ K : ℝ)⁻¹ *
      ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) +
        ∑ τ : K →+* ℂ, Real.log (archDualNorm h τ (yv q))) := by
    intro q
    obtain ⟨hloc, hht⟩ := h1 F W h n w hw K (yv q) (hyv q)
    have hex : ∃ x, yv q x ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hyv q (LinearMap.ext hne)
    rw [pointHeight, hht _ (Classical.epsilon_spec hex)]
    congr 2
    exact finsum_congr fun v ↦ by rw [(hloc v).2]

  have hfin : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) =
      (Module.finrank E K : ℝ)⁻¹ *
        ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (NumberField.HeightOneSpectrum.adicAbv K v c)) +
          ∑ q, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← finsum_log_gaussNorm_map hPne, hP,
      finsum_log_gaussNorm_mul (C_ne_zero.mpr hc) hprod,
      finsum_log_gaussNorm_prod Finset.univ (fun q ↦ ∑ k, C (yv q (w k)) * X k) hL]
    simp_rw [gaussNorm_C]

  have harch : ∑ σ : E →+* ℂ, (fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2) =
      (Module.finrank E K : ℝ)⁻¹ * ∑ τ : K →+* ℂ,
        (Real.log ‖τ c‖ + ∑ q, Real.log (archDualNorm h τ (yv q))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← sum_embeddings_restrict (K := E) (L := K)
      (fun σ : E →+* ℂ ↦ fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    have e1 : (τ.comp (algebraMap E K)).comp (algebraMap F E) = τ.comp (algebraMap F K) := by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    have e2 : P.map (τ.comp (algebraMap E K)) =
        C (τ c) * ∏ q, ∑ k, C (τ (yv q (w k))) * X k := by
      rw [← MvPolynomial.map_map, hP]
      simp only [map_mul, map_prod, map_sum, map_C, map_X]
    rw [e1, e2, h2 F W h n w hw K τ m yv hyv (τ c) ((map_ne_zero τ).mpr hc)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hfin, harch, Finset.sum_add_distrib, finsum_log_adicAbv hc, sum_log_norm_embeddings hc,
    Finset.sum_comm (f := fun τ q ↦ Real.log (archDualNorm h τ (yv q)))]
  simp_rw [hpt]
  rw [← Module.finrank_mul_finrank ℚ E K, ← Finset.mul_sum, Finset.sum_add_distrib]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawBasic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawBasic

def firstRow (N : ℕ) : (Fin 1 × Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) where
  toFun u j := u (0, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstRow_apply (N : ℕ) (u : Fin 1 × Fin N → ℂ) (j : Fin N) : firstRow N u j = u (0, j) :=
  rfl

theorem sphereNormalize_eq (N : ℕ) (u : Fin 1 × Fin N → ℂ) :
    (fun j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)) =
      ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ)⁻¹ • firstRow N u := by
  ext j
  simp [sphereNormalize, HermNorm.std_norm_eq, firstRow_apply]

theorem firstRow_eq_zero (N : ℕ) (u : Fin 1 × Fin N → ℂ) (h : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0) :
    firstRow N u = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg ‖u (0, i)‖)).mp
    (le_antisymm h (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
  ext j
  simpa [firstRow_apply] using h' j (Finset.mem_univ j)

theorem volume_firstRow_mem (N : ℕ) (S : Submodule ℂ (Fin N → ℂ)) (hS : S ≠ ⊤) :
    volume {u : Fin 1 × Fin N → ℂ | firstRow N u ∈ S} = 0 := by
  let T : Submodule ℝ (Fin 1 × Fin N → ℂ) := (S.restrictScalars ℝ).comap (firstRow N)
  have hT : T ≠ ⊤ := by
    intro h
    apply hS
    rw [eq_top_iff]
    intro v _
    let u : Fin 1 × Fin N → ℂ := fun ij ↦ v ij.2
    have hu : u ∈ T := h ▸ Submodule.mem_top
    exact hu
  exact Measure.addHaar_submodule volume T hT

end SphereLawBasic

open SphereLawBasic in

theorem SphereLawBasic.proof : SphereLawBasic.Statement := by
  intro N hN
  have hf : Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) ↦
      sphereNormalize (HermNorm.std N) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hbot : (⊥ : Submodule ℂ (Fin N → ℂ)) ≠ ⊤ := by
    intro h
    have hmem : (Pi.single ⟨0, hN⟩ 1 : Fin N → ℂ) ∈ (⊥ : Submodule ℂ (Fin N → ℂ)) :=
      h ▸ Submodule.mem_top
    simpa using congrFun ((Submodule.mem_bot ℂ).mp hmem) ⟨0, hN⟩
  have h0 : ∀ᵐ u ∂(volume[|sphereBall (HermNorm.std N) 1]), firstRow N u ≠ 0 := by
    refine cond_absolutelyContinuous.ae_le ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_firstRow_mem N ⊥ hbot)] with u hu
    simpa using hu
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [sphereLaw, ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [h0] with u hu
    have hs : 0 < ∑ i, ‖u (0, i)‖ ^ 2 := lt_of_not_ge fun h ↦ hu (firstRow_eq_zero N u h)
    have key : ∀ j, ‖sphereNormalize (HermNorm.std N) 1 u (0, j)‖ ^ 2 =
        (∑ i, ‖u (0, i)‖ ^ 2)⁻¹ * ‖u (0, j)‖ ^ 2 := by
      intro j
      have e := congrFun (sphereNormalize_eq N u) j
      rw [e]
      simp only [Pi.smul_apply, smul_eq_mul, firstRow_apply, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
        Real.sq_sqrt hs.le]
    simp only [key, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · intro S hS
    have hSm : MeasurableSet (S : Set (Fin N → ℂ)) :=
      (S.restrictScalars ℝ).closed_of_finiteDimensional.measurableSet
    rw [sphereLaw, Measure.map_apply hf hSm]
    refine measure_mono_null ?_ (cond_absolutelyContinuous (volume_firstRow_mem N S hS))
    intro u hu
    simp only [Set.mem_preimage, SetLike.mem_coe] at hu
    rw [sphereNormalize_eq] at hu
    show firstRow N u ∈ S
    by_cases hc : ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) = 0
    · have hle : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp (by exact_mod_cast hc)
      rw [firstRow_eq_zero N u hle]
      exact S.zero_mem
    · have := S.smul_mem ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) hu
      rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at this

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawUnitary
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawUnitary

def rowMap {N : ℕ} (k : ℕ) (U : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) :
    (Fin k × Fin N → ℂ) →ₗ[ℝ] (Fin k × Fin N → ℂ) where
  toFun u ij := U (fun j ↦ u (ij.1, j)) ij.2
  map_add' u v := by
    funext ij
    have : (fun j ↦ (u + v) (ij.1, j)) = (fun j ↦ u (ij.1, j)) + fun j ↦ v (ij.1, j) := rfl
    change U (fun j ↦ (u + v) (ij.1, j)) ij.2 =
      U (fun j ↦ u (ij.1, j)) ij.2 + U (fun j ↦ v (ij.1, j)) ij.2
    rw [this, map_add]
    rfl
  map_smul' r u := by
    funext ij
    have : (fun j ↦ (r • u) (ij.1, j)) = (r : ℂ) • fun j ↦ u (ij.1, j) := by
      funext j; simp [Complex.real_smul]
    change U (fun j ↦ (r • u) (ij.1, j)) ij.2 = r • U (fun j ↦ u (ij.1, j)) ij.2
    rw [this, map_smul]
    simp [Complex.real_smul]

theorem proof : SphereLawUnitary.Statement := by
  intro N U hU
  set B := sphereBall (HermNorm.std N) 1 with hBdef
  set g : (Fin 1 × Fin N → ℂ) → (Fin N → ℂ) :=
    fun u j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j) with hgdef
  set V := rowMap 1 U with hVdef
  have hrow : ∀ u i, (fun j ↦ V u (i, j)) = U (fun j ↦ u (i, j)) := fun _ _ ↦ rfl
  have hnorm : ∀ v, (HermNorm.std N).norm (U v) = (HermNorm.std N).norm v := by
    intro v; simp only [HermNorm.std_norm_eq, hU]
  have hBm : MeasurableSet B := (isOpen_sphereBall_std N).measurableSet
  have hVm : Measurable V := V.continuous_of_finiteDimensional.measurable
  have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
  have hgm : Measurable g := by
    simp only [hgdef, sphereNormalize, HermNorm.std_norm_eq]
    fun_prop
  have hpre : V ⁻¹' B = B := by
    ext u
    simp only [Set.mem_preimage, hBdef, sphereBall, Set.mem_ofPred_eq, hrow, hnorm]
  have hcomm : U ∘ g = g ∘ V := by
    funext u
    have hg : ∀ w, g w = (((HermNorm.std N).norm fun j ↦ w (0, j) : ℝ) : ℂ)⁻¹ •
        fun j ↦ w (0, j) := fun w ↦ by
      funext j; simp [hgdef, sphereNormalize]
    simp only [Function.comp_apply, hg, map_smul, hrow, hnorm]
  have hinj : Function.Injective V := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext ij
    have h1 : U (fun j ↦ u (ij.1, j)) = 0 := by rw [← hrow, hu]; rfl
    have h2 := hU (fun j ↦ u (ij.1, j))
    rw [h1] at h2
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h2
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)).mp h2.symm ij.2
      (Finset.mem_univ _)
    simpa using this
  have hdet : LinearMap.det V ≠ 0 := by
    have h := (LinearEquiv.ofInjectiveEndo V hinj).isUnit_det'
    have e : ((LinearEquiv.ofInjectiveEndo V hinj : _ ≃ₗ[ℝ] _) : _ →ₗ[ℝ] _) = V :=
      LinearMap.ext fun x ↦ by simp [LinearEquiv.coe_ofInjectiveEndo]
    rw [e] at h
    exact h.ne_zero
  have h0 : volume B ≠ 0 := by
    refine ((isOpen_sphereBall_std N).measure_pos volume ⟨0, ?_⟩).ne'
    simp [sphereBall, HermNorm.std_norm_eq]
  have htop : volume B ≠ ⊤ :=
    ((measure_mono (sphereBall_std_subset N)).trans_lt
      (isCompact_closedBall 0 1).measure_lt_top).ne
  have hvol : Measure.map V volume = (volume : Measure (Fin 1 × Fin N → ℂ)) := by
    have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Fin 1 × Fin N → ℂ)) hdet
    have hc : ENNReal.ofReal |(LinearMap.det V)⁻¹| = 1 := by
      have hB := congrArg (fun μ : Measure (Fin 1 × Fin N → ℂ) ↦ μ B) hmap
      simp only [Measure.map_apply hVm hBm, hpre, Measure.smul_apply, smul_eq_mul] at hB
      have : 1 * volume B = ENNReal.ofReal |(LinearMap.det V)⁻¹| * volume B := by
        rw [one_mul]; exact hB
      exact ((ENNReal.mul_left_inj h0 htop).mp this).symm
    rw [hmap, hc, one_smul]
  have hcond : Measure.map V (volume[|B]) = volume[|B] := by
    rw [ProbabilityTheory.cond, Measure.map_smul, ← hpre, ← Measure.restrict_map hVm hBm,
      hvol, hpre]
  show Measure.map U (Measure.map g (volume[|B])) = Measure.map g (volume[|B])
  rw [Measure.map_map hUm hgm, hcomm, ← Measure.map_map hgm hVm, hcond]

end SphereLawUnitary

end

end GroundTheory.Heights₂.Heights
end


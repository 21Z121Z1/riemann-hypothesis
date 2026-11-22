import Mathlib
import GroundTheory.LocalFields.ArtinConductor
import GroundTheory.LocalFields.ConductorTransport
import GroundTheory.LocalFields.LocalZetaIntegral

-- bundled from GroundTheory.LocalFields.ArtinConductorInduced
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem lowerIndex_conj (σ τ : L ≃ₐ[K] L) : lowerIndex K L (τ * σ * τ⁻¹) = lowerIndex K L σ := by
  rw [← lowerIndex_autCongr τ σ]
  congr 1

theorem artinCharacter_conj (σ τ : L ≃ₐ[K] L) :
    artinCharacter K L (τ * σ * τ⁻¹) = artinCharacter K L σ := by
  by_cases hσ : σ = 1
  · subst hσ
    simp
  · have h1 : τ * σ * τ⁻¹ ≠ 1 := by
      intro h
      apply hσ
      have := congrArg (fun x ↦ τ⁻¹ * x * τ) h
      simpa [mul_assoc] using this
    rw [artinCharacter_of_ne_one hσ, artinCharacter_of_ne_one h1, lowerIndex_conj]

section Induced

variable (M : IntermediateField K L)

variable {M} in
open Classical in

def inducedFun (ψ : (L ≃ₐ[M] L) → ℂ) (s : L ≃ₐ[K] L) : ℂ :=
  (Nat.card (L ≃ₐ[M] L) : ℂ)⁻¹ * ∑ t : L ≃ₐ[K] L, ∑ h : L ≃ₐ[M] L,
    if h.restrictScalars K = t⁻¹ * s * t then ψ h else 0

variable [IsGalois K L]

open Classical in

theorem artinCharacter_restrictScalars (h : L ≃ₐ[M] L) :
    (artinCharacter K L (h.restrictScalars K) : ℂ) =
      residueDegree K M * artinCharacter M L h +
        if h = 1 then (Nat.card (L ≃ₐ[M] L) : ℂ) * (residueDegree K M * differentExponent K M : ℕ)
        else 0 := by
  by_cases h1 : h = 1
  · subst h1
    rw [if_pos rfl, show (1 : L ≃ₐ[M] L).restrictScalars K = 1 from AlgEquiv.ext fun _ ↦ rfl,
      artinCharacter_one, artinCharacter_one, IsGalois.card_aut_eq_finrank,
      ← ramificationIndex_mul_residueDegree M L, residueDegree_tower K M L,
      differentExponent_tower K M L]
    push_cast
    ring
  · have h1' : h.restrictScalars K ≠ 1 := by
      intro h'
      apply h1
      ext x
      exact congrArg (fun σ : L ≃ₐ[K] L ↦ σ x) h'
    rw [if_neg h1, artinCharacter_of_ne_one h1', artinCharacter_of_ne_one h1,
      lowerIndex_restrictScalars, residueDegree_tower K M L]
    push_cast
    ring

theorem charArtinConductor_inducedFun (ψ : (L ≃ₐ[M] L) → ℂ) :
    charArtinConductor K L (inducedFun ψ) =
      ((residueDegree K M * differentExponent K M : ℕ) : ℂ) * ψ 1 +
        residueDegree K M * charArtinConductor M L ψ := by
  classical
  have hG : (Nat.card (L ≃ₐ[K] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : (Nat.card (L ≃ₐ[M] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hinner : ∀ (t : L ≃ₐ[K] L) (h : L ≃ₐ[M] L), ∑ s : L ≃ₐ[K] L,
      (if h.restrictScalars K = t⁻¹ * s * t then ψ h else 0) * (artinCharacter K L s : ℂ) =
        ψ h * artinCharacter K L (h.restrictScalars K) := by
    intro t h
    have hiff : ∀ s : L ≃ₐ[K] L,
        (h.restrictScalars K = t⁻¹ * s * t) ↔ (s = t * h.restrictScalars K * t⁻¹) := by
      intro s
      constructor
      · rintro hs
        rw [hs]
        group
      · rintro rfl
        group
    simp_rw [ite_mul, zero_mul, hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), artinCharacter_conj]
  have hpt : ∀ s : L ≃ₐ[K] L, inducedFun ψ s * (artinCharacter K L s : ℂ) =
      (Nat.card (L ≃ₐ[M] L) : ℂ)⁻¹ * ∑ t : L ≃ₐ[K] L, ∑ h : L ≃ₐ[M] L,
        (if h.restrictScalars K = t⁻¹ * s * t then ψ h else 0) * (artinCharacter K L s : ℂ) := by
    intro s
    rw [inducedFun, mul_assoc, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
  have hsum : ∑ s : L ≃ₐ[K] L, inducedFun ψ s * (artinCharacter K L s : ℂ) =
      (Nat.card (L ≃ₐ[M] L) : ℂ)⁻¹ * (Nat.card (L ≃ₐ[K] L) *
        ∑ h : L ≃ₐ[M] L, ψ h * artinCharacter K L (h.restrictScalars K)) := by
    rw [Finset.sum_congr rfl fun s _ ↦ hpt s, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl fun t _ ↦ (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun h _ ↦ hinner t h)), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hres : ∑ h : L ≃ₐ[M] L, ψ h * (artinCharacter K L (h.restrictScalars K) : ℂ) =
      residueDegree K M * ∑ h : L ≃ₐ[M] L, ψ h * artinCharacter M L h +
        ψ 1 * ((Nat.card (L ≃ₐ[M] L) : ℂ) * (residueDegree K M * differentExponent K M : ℕ)) := by
    simp_rw [artinCharacter_restrictScalars, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun h _ ↦ by ring
  rw [charArtinConductor, hsum, hres, charArtinConductor]
  field_simp
  ring

end Induced

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalZetaTate
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

section Symmetric

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem integral_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ x, f x * localFourier μ ψ g (x * y) ∂μ = ∫ x, g x * localFourier μ ψ f (x * y) ∂μ := by
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hfi := integrable_of_mem_schwartzBruhat μ hf
  have hgi := integrable_of_mem_schwartzBruhat μ hg
  let G : K → K → ℂ := fun x z => f x * (g z * (ψ (z * (x * y)) : ℂ))
  have hG : Integrable (Function.uncurry G) (μ.prod μ) := by
    have hdom : Integrable (fun p : K × K => ‖f p.1‖ * ‖g p.2‖) (μ.prod μ) :=
      hfi.norm.mul_prod hgi.norm
    refine hdom.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun p => ?_)
    · exact (hf.1.continuous.comp continuous_fst).mul ((hg.1.continuous.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul (continuous_fst.mul continuous_const))))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have e1 : ∫ x, f x * localFourier μ ψ g (x * y) ∂μ = ∫ x, ∫ z, G x z ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [localFourier, G]
    rw [integral_const_mul]
  have e2 : ∫ x, g x * localFourier μ ψ f (x * y) ∂μ = ∫ z, ∫ x, G x z ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [localFourier, G]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show x * (z * y) = z * (x * y) by ring]
    ring
  rw [e1, e2, integral_integral_swap hG]

end Symmetric

section Multiplicative

theorem haarIntegers_singleton_zero : haarIntegers K {0} = 0 := by
  have hq : (1 : ℝ≥0) < (residueCard K : ℝ≥0) := one_lt_residueCard_nnreal
  have ht : Tendsto (fun n : ℕ => (((residueCard K : ℝ≥0) ^ (-(n : ℤ)) : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 0) := by
    rw [← ENNReal.coe_zero, ENNReal.tendsto_coe]
    have e : (fun n : ℕ => (residueCard K : ℝ≥0) ^ (-(n : ℤ))) =
        fun n : ℕ => ((residueCard K : ℝ≥0)⁻¹) ^ n := by
      funext n
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [e]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (inv_lt_one_of_one_lt₀ hq)
  refine le_antisymm (ge_of_tendsto' ht fun n => ?_) (by simp)
  rw [← haarIntegers_valBall]
  exact measure_mono (Set.singleton_subset_iff.mpr (zero_mem _))

theorem integral_multHaar_mul_modulus (h : K → ℂ) :
    ∫ u, h u * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      (multHaarConst K).toReal * ∫ x, h x ∂haarIntegers K := by
  rw [integral_multHaar (fun x => h x * ((modulus x : ℝ) : ℂ)), Complex.real_smul]
  congr 1
  have hae : ∀ᵐ x ∂haarIntegers K, x ∈ ({0}ᶜ : Set K) := by
    rw [ae_iff]
    simpa using haarIntegers_singleton_zero (K := K)
  conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have hm : ((modulus x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  rw [Complex.real_smul, Complex.ofReal_inv, mul_comm, mul_assoc, mul_inv_cancel₀ hm, mul_one]

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem integral_multHaar_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ u, f u * localFourier μ ψ g ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      ∫ u, g u * localFourier μ ψ f ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K := by
  rw [integral_multHaar_mul_modulus (fun x => f x * localFourier μ ψ g (x * y)),
    integral_multHaar_mul_modulus (fun x => g x * localFourier μ ψ f (x * y))]
  congr 1
  have hμ := eq_smul_haarIntegers μ
  have key := integral_mul_localFourier_comm μ hψ hf hg y
  have hc : (μ (𝒪[K] : Set K)).toReal ≠ 0 := by
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
    · rw [← coe_valBall_zero]
      exact ((isOpen_valBall 0).measure_pos μ ⟨0, zero_mem _⟩).ne'
    · rw [← coe_valBall_zero]
      exact (isCompact_valBall 0).measure_lt_top.ne
  have hJ : ∀ F : K → ℂ, ∫ x, F x ∂μ = ((μ (𝒪[K] : Set K)).toReal : ℂ) * ∫ x, F x ∂haarIntegers K :=
    fun F => by
      conv_lhs => rw [hμ]
      rw [integral_smul_measure, Complex.real_smul]
  rw [hJ, hJ] at key
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc) key

end Multiplicative

section Tate

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
  (hψ1 : ψ ≠ 1) {χ : Kˣ →* ℂˣ} (hχ : Continuous χ)
include hψ hψ1 hχ

theorem localZeta_mul_localZeta_fourier_eq {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      ∫ y, ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        ∫ x, f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)
          ∂multHaar K ∂multHaar K := by
  set F₁ : Kˣ → ℂ := fun u => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s
  set G₁ : Kˣ → ℂ := fun u => localFourier μ ψ g u * (((χ⁻¹) u : ℂˣ) : ℂ) *
    ((modulus (u : K) : ℝ) : ℂ) ^ (1 - s)
  have hF₁ : Integrable F₁ (multHaar K) := integrable_localZeta hf hχ hs1
  have hG₁ : Integrable G₁ (multHaar K) :=
    integrable_localZeta (localFourier_mem_schwartzBruhat μ hψ hψ1 hg) (continuous_quasiChar_inv hχ)
      (by rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]; linarith)
  have hP : Integrable (fun p : Kˣ × Kˣ => F₁ p.1 * G₁ p.2) ((multHaar K).prod (multHaar K)) :=
    hF₁.mul_prod hG₁
  have hH : Integrable (Function.uncurry fun x y : Kˣ => F₁ x * G₁ (x * y))
      ((multHaar K).prod (multHaar K)) :=
    (measurePreserving_prod_mul (multHaar K) (multHaar K)).integrable_comp_of_integrable hP
  have hpt : ∀ x y : Kˣ, F₁ x * G₁ (x * y) =
      ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        (f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)) := by
    intro x y
    have hx0 : ((modulus (x : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos x.ne_zero).ne'
    have e1 : (((χ⁻¹) (x * y) : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ)⁻¹ * ((χ y : ℂˣ) : ℂ)⁻¹ := by
      rw [MonoidHom.inv_apply, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val]
    have e2 : ((modulus ((x * y : Kˣ) : K) : ℝ) : ℂ) ^ (1 - s) =
        ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) := by
      rw [Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    have e3 : ((modulus (x : K) : ℝ) : ℂ) ^ s * ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) =
        ((modulus (x : K) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hx0, add_sub_cancel, Complex.cpow_one]
    have hχx : ((χ x : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (χ x).ne_zero
    simp only [F₁, G₁]
    rw [e1, e2, Units.val_mul]
    calc f x * ((χ x : ℂˣ) : ℂ) * ((modulus (x : K) : ℝ) : ℂ) ^ s *
          (localFourier μ ψ g ((x : K) * (y : K)) * (((χ x : ℂˣ) : ℂ)⁻¹ * ((χ y : ℂˣ) : ℂ)⁻¹) *
            (((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s)))
        = (((χ x : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ)⁻¹) *
            (((modulus (x : K) : ℝ) : ℂ) ^ s * ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s)) *
            (((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
              (f x * localFourier μ ψ g ((x : K) * (y : K)))) := by ring
      _ = _ := by rw [hχx, e3]; ring
  calc localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s)
      = (∫ x, F₁ x ∂multHaar K) * ∫ y, G₁ y ∂multHaar K := rfl
    _ = ∫ x, F₁ x * ∫ y, G₁ y ∂multHaar K ∂multHaar K := (integral_mul_const _ _).symm
    _ = ∫ x, ∫ y, F₁ x * G₁ (x * y) ∂multHaar K ∂multHaar K := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_const_mul, integral_mul_left_eq_self G₁ x]
    _ = ∫ y, ∫ x, F₁ x * G₁ (x * y) ∂multHaar K ∂multHaar K := integral_integral_swap hH
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hpt]
        rw [integral_const_mul]

theorem localZeta_mul_localZeta_fourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      localZeta g χ s * localZeta (localFourier μ ψ f) χ⁻¹ (1 - s) := by
  rw [localZeta_mul_localZeta_fourier_eq μ hψ hψ1 hχ hf hg hs1 hs2,
    localZeta_mul_localZeta_fourier_eq μ hψ hψ1 hχ hg hf hs1 hs2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_multHaar_mul_localFourier_comm μ hψ hf hg]

end Tate

end GroundTheory.LocalField
end
end


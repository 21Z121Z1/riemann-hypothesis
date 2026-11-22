import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFGTorus

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  unfold mp
  rw [Units.val_mul, GroundTheory.LocalField.modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem mp_add (x : Fˣ) (a b : ℂ) : mp x (a + b) = mp x a * mp x b := by
  unfold mp
  refine Complex.cpow_add _ _ ?_
  have := GroundTheory.LocalField.modulus_ne_zero x.ne_zero
  exact_mod_cast this

theorem mp_zero (x : Fˣ) : mp x 0 = 1 := by simp [mp]

theorem blk_dg (h : Matrix (Fin 2) (Fin 2) F) (t₁ t₂ : Fˣ) (x : Fin 2 → F) :
    h * blk x * ((dg t₁ t₂ 1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      col3 (h * ((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) (h *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, col3, dg, dg2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

theorem integral_mulVec (ψ : AddChar F Circle) (h : GL (Fin 2) F) (f : (Fin 2 → F) → ℂ) :
    ∫ x, f ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ∂vol2 ψ =
      mp (GeneralLinearGroup.det h) (-1) * ∫ y, f y ∂vol2 ψ := by
  have key := GlobalTheory.WeilM.integral_comp_mulVec (selfDualMeasure ψ) h f
  have hm : ((distribHaarChar F (GeneralLinearGroup.det h) : ℝ) : ℂ) = mp (GeneralLinearGroup.det h) 1 := by
    rw [distribHaarChar_eq_modulus]; simp [mp]
  rw [hm] at key
  unfold vol2
  rw [← key, ← mul_assoc, ← mp_add]
  simp [mp_zero]

theorem inn_dg (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F) (t₁ t₂ : Fˣ) :
    inn ψ Φ h (dg t₁ t₂ 1) = mp (GeneralLinearGroup.det h) (-1) *
      pft ψ Φ ((h * dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) := by
  unfold pft
  rw [← integral_mulVec ψ h]
  unfold inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ∑ j, (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j *
      ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) j = x 1 := by
    have e : (t₂ : F) • (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 =
        (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) 1 := by
      ext j
      simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) *
        (h : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul]
      simp
    have e3 : ∀ j, (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j =
        (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) 1 j :=
      fun j => congrFun e j
    simp only [e3]
    have e4 := congrFun (Matrix.mulVec_mulVec x (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) (h : Matrix (Fin 2) (Fin 2) F)) 1
    rw [e2, Matrix.one_mulVec] at e4
    exact e4
  have hb := blk_dg (h : Matrix (Fin 2) (Fin 2) F) t₁ t₂ x
  rw [← Units.val_mul] at hb
  beta_reduce
  rw [hb, hx]

theorem gtorus : Ad3.LFS.GTorus := by
  intro F _ _ _ _ _ _ ψ ν W' Φ _ t₁ t₂
  have hdet : GeneralLinearGroup.det (dg t₁ t₂ 1) = t₁ * t₂ := by
    ext
    simp [dg, Matrix.det_fin_three]
  have hdet2 : GeneralLinearGroup.det (dg2 t₁ t₂) = t₁ * t₂ := by
    ext
    simp [dg2, Matrix.det_fin_two]
  unfold Wp
  rw [hdet]
  set G : GL (Fin 2) F → ℂ := fun k => W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
      pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) with hGd
  have alg : ∀ w a b p c d : ℂ, c * d = 1 → w * a * (b * p) = c * (w * (a * b * d) * p) := by
    intro w a b p c d hcd
    linear_combination (-(w * a * b * p)) * hcd
  have hpt : ∀ h : GL (Fin 2) F, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (dg t₁ t₂ 1) =
      mp (t₁ * t₂) (-(1 / 2)) * G (h * dg2 t₁ t₂) := by
    intro h
    have hw : dg2 t₁ t₂ * (h * dg2 t₁ t₂)⁻¹ = h⁻¹ := by group
    have hm : mp (GeneralLinearGroup.det (h * dg2 t₁ t₂)) (1 / 2) =
        mp (GeneralLinearGroup.det h) (3 / 2) * mp (GeneralLinearGroup.det h) (-1) * mp (t₁ * t₂) (1 / 2) := by
      rw [map_mul, hdet2, mp_mul, ← mp_add]
      norm_num
    have hc : mp (t₁ * t₂) (-(1 / 2)) * mp (t₁ * t₂) (1 / 2) = 1 := by
      rw [← mp_add]
      simp [mp_zero]
    rw [inn_dg, hGd]
    beta_reduce
    rw [hw, hm]
    exact alg _ _ _ _ _ _ hc
  haveI : (hG ψ).IsMulRightInvariant := by
    unfold hG
    infer_instance
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_mul_right_eq_self (μ := hG ψ) G (dg2 t₁ t₂), ← mul_assoc, ← mp_add]
  norm_num

end GlobalTheory.CompanionTheory.LFGTorus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusReduction
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFTor

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem norm_mp_half (x : Fˣ) :
    ‖mp x (1 / 2)‖ = (modulus (x : F) : ℝ) ^ (1 / 2 : ℝ) := by
  have ht : 0 < (modulus (x : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos x.ne_zero
  unfold mp
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  norm_num

theorem rpow_torus {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a * b) ^ (1 / 2 : ℝ) * (a ^ (1 / 4 : ℝ) * b ^ (-(1 / 2) : ℝ)) = a ^ (3 / 4 : ℝ) := by
  rw [Real.mul_rpow ha.le hb.le, Real.rpow_neg hb.le]
  have hb' : b ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have : a ^ (3 / 4 : ℝ) = a ^ (1 / 2 : ℝ) * a ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add ha]
    norm_num
  rw [this]
  field_simp

theorem gTor : Ad3.LFS.GTor := by
  intro hT hF hI F _ _ _ _ _ _ ψ ν W' Φ hyp
  obtain ⟨hs, hu, ⟨V', hV, hW⟩, hΦ⟩ := id hyp
  obtain ⟨C₁, R, h1⟩ := hF F ψ hs Φ hΦ
  obtain ⟨C₂, h2⟩ := hI F ψ hs ν hu V' hV W' hW R
  refine ⟨max C₁ 0 * max C₂ 0, fun t₁ t₂ => ?_⟩
  obtain ⟨hint, hle⟩ := h2 t₁ t₂
  have hm1 : 0 < (modulus (t₁ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₁.ne_zero
  have hm2 : 0 < (modulus (t₂ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₂.ne_zero
  have hC₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  set G : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)
    with hGd
  have hG0 : ∀ k, 0 ≤ G k := fun k =>
    Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) k
  have hpt : ∀ k : GL (Fin 2) F,
      ‖W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)‖ ≤
        max C₁ 0 * G k := by
    intro k
    by_cases hp : pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) = 0
    · rw [hp, mul_zero, norm_zero]
      exact mul_nonneg hC₁ (hG0 k)
    · obtain ⟨hb, hsup⟩ := h1 (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)
      obtain ⟨hk, hξ⟩ := hsup hp
      have hmem : k ∈ om R t₂ := ⟨hk, hξ⟩
      have hGk : G k = ‖W' (dg2 t₁ t₂ * k⁻¹)‖ *
          (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hGd, Set.indicator_of_mem hmem]
      rw [norm_mul, norm_mul, norm_mp_half, ← hGk, mul_comm]
      exact mul_le_mul ((hb).trans (le_max_left _ _)) le_rfl
        (by rw [hGk]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) hC₁
  have hbound : ‖∫ k, W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ∂hG ψ‖ ≤
      max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) *
        (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := integral_mono_of_nonneg (μ := hG ψ)
      (Filter.Eventually.of_forall fun k => norm_nonneg _)
      (hint.const_mul (max C₁ 0)) (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    refine hle.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (Real.rpow_nonneg hm1.le _) (Real.rpow_nonneg hm2.le _))
  rw [hT F ψ ν W' Φ hyp t₁ t₂, norm_mul, norm_mp_half, Units.val_mul, GroundTheory.LocalField.modulus_mul,
    NNReal.coe_mul]
  calc _ ≤ ((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
        (max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) *
          (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = max C₁ 0 * max C₂ 0 * (((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
          ((modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by ring
    _ = _ := by rw [rpow_torus hm1 hm2]

end GlobalTheory.CompanionTheory.LFTor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingNormMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

section Ring

open scoped Pointwise

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem map_mul_unit (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (u : Aˣ) :
    μ.map (fun x => (u : A) * x) = (distribHaarChar A u)⁻¹ • μ := by
  have hm : Measurable fun x : A => (u : A) * x := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun x : A => (u : A) * x) ⁻¹' B = u⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, map_inv]
  rfl

theorem exists_pos_finite (μ : Measure A) [μ.IsAddHaarMeasure] :
    ∃ K : Set A, μ K ≠ 0 ∧ μ K ≠ ∞ := by
  obtain ⟨K, hK, hn⟩ := exists_compact_mem_nhds (0 : A)
  refine ⟨K, ?_, hK.measure_lt_top.ne⟩
  exact (Measure.measure_pos_of_mem_nhds μ hn).ne'

theorem smul_inj (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have e := congrArg (fun m : Measure A => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem char_map (s : A ≃+* A) (hs : Continuous s) (hs' : Continuous s.symm) (u : Aˣ) :
    distribHaarChar A (Units.map (s : A →* A) u) = distribHaarChar A u := by
  let H : A ≃ₜ A := ⟨s.toEquiv, hs, hs'⟩
  let μ : Measure A := Measure.addHaar
  have : (μ.map H).IsAddHaarMeasure := s.toAddEquiv.isAddHaarMeasure_map μ hs hs'
  have : (μ.map H).Regular := Measure.Regular.map H
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have hap : ∀ S : Set A, (μ.map H) S = μ (H ⁻¹' S) := fun S =>
    H.toMeasurableEquiv.map_apply S
  have hpre : H ⁻¹' (H '' K) = K := H.injective.preimage_image K
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map H) (s := H '' K)
    (by rwa [hap, hpre]) (by rwa [hap, hpre]) ?_
  rw [hap, hap, hpre, distribHaarChar_mul]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, hy⟩
    refine ⟨k, hk, H.injective ?_⟩
    rw [← hy]
    simp [H, Units.smul_def]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨H k, ⟨k, hk, rfl⟩, ?_⟩
    simp [H, Units.smul_def]

end Ring

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

theorem coordK_map_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  intro F E _ _ _ _ _ σ hσ d b v lam hlam c t w hc ht hnorm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, hsc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set μ := coordK (Fv F v) b lam with hμ
  haveI : μ.Regular := inferInstance
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigma_sigma σ hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let s : (Fv F v ⊗[F] E) ≃+* (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, invFun := sigR (Fv F v) σ, left_inv := hss, right_inv := hss,
      map_mul' := map_mul _, map_add' := map_add _ }
  let u : (Fv F v ⊗[F] E)ˣ := hc.unit
  have hu : (u : Fv F v ⊗[F] E) = c := hc.unit_spec
  have hchar := char_map s hsc hsc u
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hqv : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero, hqv] at hnorm
    exact inv_ne_zero (pow_ne_zero w hq) hnorm.symm
  have hk : ‖t‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ w := by
    rw [hnorm, hqv, inv_pow]
  have h1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam t ht0 w hk
  have h2 := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam t ht0 _ h1
  have h3 := map_mul_unit μ (Units.map (s : _ →* _) u * u)
  have hval : ((Units.map (s : _ →* _) u * u : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
    rw [ht, ← hu]
    rfl
  rw [hval, h2, map_mul, hchar] at h3
  have h4 := smul_inj μ h3
  have h5 : (distribHaarChar (Fv F v ⊗[F] E) u)⁻¹ = qv v ^ w := by
    refine (pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 ?_
    rw [inv_pow, pow_two]
    exact h4.symm
  rw [← h5, ← map_mul_unit μ u, hu]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandard
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero

theorem mass_dilated_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b v lam hlam m hm a e ha h1 h2
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have hnorm := GlobalTheory.CompanionTheory.SW.Dil.norm_natCast v a e ha h1 h2
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ht : (a : Fv F v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_ne_zero e (inv_ne_zero hq)) hnorm.symm
  have ht2 : (a : Fv F v) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e) := by
    rw [norm_pow, hnorm, ← pow_mul, mul_comm]
  have hs1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht e hnorm
  have hs2 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht2 (2 * e) hnorm2
  set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E :=
    fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf
  have hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E) := map_natCast _ _
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam _ ht _ hs1
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    change IsUnit (a : Fv F v ⊗[F] E)
    rw [← hcast]
    exact ht.isUnit.map _
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]
    rw [Subsingleton.elim p 0, mul_comm]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S => (a ^ 2) • S
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) *
        (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    change (a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _
    rw [nsmul_eq_mul, map_pow, hcast]
    push_cast
    rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    exact (continuous_nsmul (a ^ 2)).measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    have hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := map_natCast _ _
    rw [hτe, map_pow, hcast, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    exact smul_zero _
  rw [hτs] at key
  have hA : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.SW.Growth.measurable_latV b v
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' (latV b v)) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2)) := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [this]
    ring
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    refine pow_ne_zero _ ?_
    rw [hqdef]
    exact_mod_cast hq
  have key3 := (ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2
  have hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} =
      (fun X => rmul (Fv F v) X g) ⁻¹' (latV b v) := by
    rw [hrm]
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]
  have hof : ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) =
      ((q ^ (e * (2 * M - 2)) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hset, ← key3, hof]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_of_dual_pairing : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K, (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) → a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientRankZeroStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_rank_zero : ∀ (D : D7) (p : ℕ) (hn : 0 + p = p) (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p), pc M m ψ b₀ F g = F g := by
  first | exact @GlobalTheory.CompanionTheory.PcZero.pc_eq | exact GlobalTheory.CompanionTheory.PcZero.pc_eq | (intros; apply GlobalTheory.CompanionTheory.PcZero.pc_eq <;> assumption)
end


import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0612
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0609
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSeventhOfSecond
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R Ad3.SchwartzSpaceL2
open scoped ValuativeRel ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RSPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem chF_coe (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) : chF c s (u : F) = ((c u : ℂˣ) : ℂ) * mp u s := by
  simp [chF, u.ne_zero]

theorem measurable_chF {c : Fˣ →* ℂˣ} (hc : Continuous c) (s : ℂ) : Measurable (chF c s) := by
  have hcont : Continuous (fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s) := by
    refine (Units.continuous_val.comp hc).mul ?_
    unfold mp
    refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
    exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)
  have he : chF c s = Function.extend (Units.val : Fˣ → F)
      (fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s) (fun _ => 0) := by
    funext t
    by_cases h : t = 0
    · subst h
      rw [Function.extend_apply']
      · simp [chF]
      · rintro ⟨u, hu⟩
        exact u.ne_zero hu
    · have := Units.val_injective.extend_apply (fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s)
        (fun _ => (0 : ℂ)) (Units.mk0 t h)
      rw [Units.val_mk0] at this
      rw [this, ← chF_coe, Units.val_mk0]
  rw [he]
  exact measurableEmbedding_units_val.measurable_extend hcont.measurable measurable_const

theorem mp_mul_mp_one (u : Fˣ) (σ : ℂ) : mp u (σ - 1) * mp u 1 = mp u σ := by
  unfold mp
  have h0 : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos u.ne_zero).ne'
  rw [← Complex.cpow_add _ _ h0, sub_add_cancel]

theorem integrable_mul_chF (ψ : AddChar F Circle) {g : F → ℂ} (hg : g ∈ schwartzBruhat F)
    {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {σ : ℂ} (hσ : 0 < σ.re) :
    Integrable (fun t => g t * chF c (σ - 1) t) (selfDualMeasure ψ) := by
  set h : F → ℂ := fun t => g t * chF c (σ - 1) t with hh
  have hm : Measurable h := hg.1.continuous.measurable.mul (measurable_chF hc.1 _)
  have hZ := integrable_localZeta hg hc.1 (s := σ)
    (by rw [GlobalTheory.CompanionTheory.TateFE.quasiCharExponent_eq_zero_of_unit hc]; simpa using hσ)
  have hfin := hZ.2
  rw [hasFiniteIntegral_iff_enorm] at hfin
  have hG : Measurable (fun x : F => ‖h x‖ₑ * (modulus x : ℝ≥0∞)) :=
    hm.enorm.mul measurable_modulus.coe_nnreal_ennreal
  have h1 := lintegral_multHaar hG
  have h2 : ∫⁻ u : Fˣ, ‖h u‖ₑ * (modulus (u : F) : ℝ≥0∞) ∂multHaar F =
      ∫⁻ u : Fˣ, ‖g u * ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ σ‖ₑ ∂multHaar F := by
    refine lintegral_congr fun u => ?_
    have e : g u * ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ σ =
        h u * ((modulus (u : F) : ℝ) : ℂ) := by
      have := mp_mul_mp_one u σ
      simp only [hh, chF_coe]
      have h3 : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by simp [mp]
      rw [h3] at this
      have h4 : ((modulus (u : F) : ℝ) : ℂ) ^ σ = mp u σ := rfl
      rw [h4, ← this]
      ring
    have hn : ‖((modulus (u : F) : ℝ) : ℂ)‖ₑ = (modulus (u : F) : ℝ≥0∞) := by
      rw [enorm_eq_nnnorm]
      congr 1
      ext
      simp
    rw [e, enorm_mul (h u), hn]
  have h5 : ∫⁻ x in ({0}ᶜ : Set F), ((modulus x : ℝ≥0∞))⁻¹ * (‖h x‖ₑ * (modulus x : ℝ≥0∞))
      ∂haarIntegers F = ∫⁻ x, ‖h x‖ₑ ∂haarIntegers F := by
    have hae : ∀ᵐ x ∂haarIntegers F, x ∈ ({0}ᶜ : Set F) := by
      rw [ae_iff]
      simpa using haarIntegers_singleton_zero (K := F)
    conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
    refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
    have a0 : (modulus x : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero hx)
    rw [mul_comm (‖h x‖ₑ), ← mul_assoc, ENNReal.inv_mul_cancel a0 ENNReal.coe_ne_top, one_mul]
  rw [h2, h5] at h1
  have h6 : ∫⁻ x, ‖h x‖ₑ ∂haarIntegers F < ∞ := by
    rw [h1] at hfin
    rw [lt_top_iff_ne_top]
    intro this
    rw [this, ENNReal.mul_top multHaarConst_ne_zero] at hfin
    exact lt_irrefl _ hfin
  have h7 : Integrable h (haarIntegers F) :=
    ⟨hm.aestronglyMeasurable, by rw [hasFiniteIntegral_iff_enorm]; exact h6⟩
  unfold selfDualMeasure
  exact h7.smul_measure_nnreal

theorem mul_integral_chF {ψ : AddChar F Circle} {C : ℂ}
    (hC : ∀ G : F → ℂ, ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = C * ∫ t, G t ∂selfDualMeasure ψ)
    (g : F → ℂ) (c : Fˣ →* ℂˣ) (σ : ℂ) :
    C * ∫ t, g t * chF c (σ - 1) t ∂selfDualMeasure ψ = localZeta g c σ := by
  rw [← hC]
  unfold localZeta
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h4 : ((modulus (u : F) : ℝ) : ℂ) ^ σ = mp u σ := rfl
  simp only [chF_coe, h4, ← mp_mul_mp_one u σ]
  ring

theorem key_one {ψ : AddChar F Circle} (hψ : IsStd ψ) {C : ℂ} (hC0 : C ≠ 0)
    (hC : ∀ G : F → ℂ, ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = C * ∫ t, G t ∂selfDualMeasure ψ)
    {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ) {g : F → ℂ} (hg : g ∈ schwartzBruhat F) {s : ℂ} (hs : Strip s) :
    ∫ t, localFourier (selfDualMeasure ψ) ψ g t * chF χ⁻¹ (-s) t ∂selfDualMeasure ψ =
      gam ψ χ s * ∫ t, g t * chF χ (s - 1) t ∂selfDualMeasure ψ := by
  have h1 := mul_integral_chF hC (localFourier (selfDualMeasure ψ) ψ g) χ⁻¹ (1 - s)
  have h2 := mul_integral_chF hC g χ s
  have h3 := GlobalTheory.CompanionTheory.TateFE.first_form hψ hχ hg hs.1 hs.2
  have e : (1 - s - 1 : ℂ) = -s := by ring
  rw [e] at h1
  apply mul_left_cancel₀ hC0
  rw [h1, h3, ← h2]
  ring

theorem integral_plane_measure_product (ψ : AddChar F Circle) (a b : F → ℂ) :
    ∫ r, a (r 0) * b (r 1) ∂m2 ψ =
      (∫ t, a t ∂selfDualMeasure ψ) * ∫ t, b t ∂selfDualMeasure ψ := by
  have := integral_fintype_prod_eq_prod (𝕜 := ℂ) (ι := Fin 2) (E := fun _ => F)
    (μ := fun _ => selfDualMeasure ψ) (fun i => ![a, b] i)
  simpa [Fin.prod_univ_two, m2] using this

theorem integrable_plane_measure_product (ψ : AddChar F Circle) {a b : F → ℂ}
    (ha : Integrable a (selfDualMeasure ψ)) (hb : Integrable b (selfDualMeasure ψ)) :
    Integrable (fun r : Fin 2 → F => a (r 0) * b (r 1)) (m2 ψ) := by
  have := Integrable.fintype_prod (𝕜 := ℂ) (ι := Fin 2) (E := F)
    (μ := fun _ => selfDualMeasure ψ) (f := fun i => ![a, b] i)
    (fun i => by fin_cases i <;> simpa)
  simpa [Fin.prod_univ_two, m2] using this

theorem integral_plane_measure_sum_products (ψ : AddChar F Circle) {n : ℕ} {A B : Fin n → F → ℂ}
    (hA : ∀ i, Integrable (A i) (selfDualMeasure ψ)) (hB : ∀ i, Integrable (B i) (selfDualMeasure ψ)) :
    ∫ r, ∑ i, A i (r 0) * B i (r 1) ∂m2 ψ =
      ∑ i, (∫ t, A i t ∂selfDualMeasure ψ) * ∫ t, B i t ∂selfDualMeasure ψ := by
  rw [integral_finset_sum _ fun i _ => integrable_plane_measure_product ψ (hA i) (hB i)]
  exact Finset.sum_congr rfl fun i _ => integral_plane_measure_product ψ _ _

theorem integrable_mul_char {ψ : AddChar F Circle} (hψ : Continuous ψ) {g : F → ℂ}
    (hg : g ∈ schwartzBruhat F) (y : F) :
    Integrable (fun x => g x * (ψ (x * y) : ℂ)) (selfDualMeasure ψ) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hg.1.continuous.mul ?_) hg.2.mul_right
  exact continuous_induced_dom.comp (hψ.comp (continuous_id.mul continuous_const))

theorem plane_fourier_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) {n : ℕ} {a b : Fin n → F → ℂ}
    (ha : ∀ i, a i ∈ schwartzBruhat F) (hb : ∀ i, b i ∈ schwartzBruhat F) (r : Fin 2 → F) :
    ∫ r', (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ =
      ∑ i, localFourier (selfDualMeasure ψ) ψ (a i) (r 0) *
        localFourier (selfDualMeasure ψ) ψ (b i) (r 1) := by
  have e : ∀ r' : Fin 2 → F, (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) =
      ∑ i, (fun x => a i x * (ψ (x * r 0) : ℂ)) (r' 0) * (fun x => b i x * (ψ (x * r 1) : ℂ)) (r' 1) := by
    intro r'
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SchwartzSpaceL2.pt, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [e]
  rw [integral_plane_measure_sum_products ψ (fun i => integrable_mul_char hψ (ha i) _)
    (fun i => integrable_mul_char hψ (hb i) _)]
  rfl

theorem a7 : Ad3.R.A2 → Ad3.R.A7 := by
  intro hA2 F _ _ _ _ _ _ ψ hψ χ₁ χ₂ h₁ h₂ f hf s hs
  obtain ⟨C, hC0, hC, -⟩ := hA2 F ψ hψ
  obtain ⟨n, a, b, hab, rfl⟩ := GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt F f hf
  have ha : ∀ i, a i ∈ schwartzBruhat F := fun i => (hab i).1
  have hb : ∀ i, b i ∈ schwartzBruhat F := fun i => (hab i).2
  have hs' : 0 < (1 - s).re := by
    have := hs.2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have e1 : (1 - s - 1 : ℂ) = -s := by ring
  have hT : ∀ {g : F → ℂ}, g ∈ schwartzBruhat F →
      localFourier (selfDualMeasure ψ) ψ g ∈ schwartzBruhat F := fun hg =>
    localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ.1 hψ.2.1 hg
  have hI : ∀ {g : F → ℂ} {χ : Fˣ →* ℂˣ}, g ∈ schwartzBruhat F → IsUnit1 χ →
      Integrable (fun t => localFourier (selfDualMeasure ψ) ψ g t * chF χ⁻¹ (-s) t)
        (selfDualMeasure ψ) := by
    intro g χ hg hχ
    have hχ' : IsUnit1 χ⁻¹ := ⟨continuous_quasiChar_inv hχ.1, fun x => by
      simp [hχ.2]⟩
    have := integrable_mul_chF ψ (hT hg) hχ' hs'
    rwa [e1] at this
  have hL : ∫ r, (∫ r', (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) *
      (chF χ₁⁻¹ (-s) (r 0) * chF χ₂⁻¹ (-s) (r 1)) ∂m2 ψ =
      ∑ i, (∫ t, localFourier (selfDualMeasure ψ) ψ (a i) t * chF χ₁⁻¹ (-s) t ∂selfDualMeasure ψ) *
        ∫ t, localFourier (selfDualMeasure ψ) ψ (b i) t * chF χ₂⁻¹ (-s) t ∂selfDualMeasure ψ := by
    rw [← integral_plane_measure_sum_products ψ (fun i => hI (ha i) h₁) (fun i => hI (hb i) h₂)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only []
    rw [plane_fourier_sum hψ.1 ha hb r, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hR : ∫ r, (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r * (chF χ₁ (s - 1) (r 0) * chF χ₂ (s - 1) (r 1)) ∂m2 ψ =
      ∑ i, (∫ t, a i t * chF χ₁ (s - 1) t ∂selfDualMeasure ψ) *
        ∫ t, b i t * chF χ₂ (s - 1) t ∂selfDualMeasure ψ := by
    rw [← integral_plane_measure_sum_products ψ (fun i => integrable_mul_chF ψ (ha i) h₁ hs.1)
      (fun i => integrable_mul_chF ψ (hb i) h₂ hs.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only []
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SchwartzSpaceL2.pt]
    ring
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key_one hψ hC0 hC h₁ (ha i) hs, key_one hψ hC0 hC h₂ (hb i) hs]
  ring

end GlobalTheory.CompanionTheory.RSPlane

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergUnfolding
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.BottomRowCoordinates

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem continuous_Dt : Continuous Dt :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det ℚ 2))

theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp only [Dt, map_mul, md_mul]

theorem detModulus_rational (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  have h : GeneralLinearGroup.det (dia2 γ) = IdeleGroup.diagonal ℚ (GeneralLinearGroup.det γ) := by
    ext
    rw [IdeleGroup.coe_diagonal, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  simp only [Dt, md, h, IdeleGroup.ideleModule_diagonal]
  rfl

theorem detModulus_unipotent (x : 𝔸[ℚ]) : Dt (uni2 x) = 1 := by
  have h : GeneralLinearGroup.det (uni2 x) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, uni2, Matrix.det_fin_two]
  simp [Dt, md, h]

theorem detModulus_diag (a b : Jd) : Dt (dg2 a b) = md a * md b := by
  have h : GeneralLinearGroup.det (dg2 a b) = a * b := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, dg2, Matrix.det_fin_two]
  simp [Dt, h, md_mul]

theorem Dt_K (κ : KA) : Dt κ.1 = 1 := by
  have h := GroundTheory.Automorphic.Adele2.ideleModule_det_of_mem_maxCompact κ.2
  simp [Dt, md, h]

theorem Dt_pt (x : 𝔸[ℚ]) (a z : Jd) (κ : KA) : Dt (pt x a z κ.1) = md a * md z ^ 2 := by
  simp only [pt, Dt_mul, detModulus_unipotent, detModulus_diag, Dt_K]
  have : md 1 = 1 := by simp [md]
  rw [this]; ring

theorem central_diagonal_commute (z : Jd) (g : G2) : g * dg2 z z = dg2 z z * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem pt_eq (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    pt x a z κ = dg2 z z * (uni2 x * dg2 a 1 * κ) := by
  simp only [pt]
  rw [central_diagonal_commute z (uni2 x * dg2 a 1)]
  group

theorem row_rational_matrix_mul (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (g : G2) :
    Ad3.R.row ξ (dia2 γ * g) = Ad3.R.row (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ)) g := by
  simp only [Ad3.R.row, Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, AdelicGLn.diagonal_apply]

def rowEquiv (γ : GL (Fin 2) ℚ) : NZ ≃ NZ where
  toFun ξ := ⟨ξ.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ), fun h => ξ.2 (by
    have := congrArg (· ᵥ* ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using this)⟩
  invFun ξ := ⟨ξ.1 ᵥ* ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ), fun h => ξ.2 (by
    have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using this)⟩
  left_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul, ← Units.val_mul])
  right_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul, ← Units.val_mul])

theorem th_linv (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) : LInv (th Φ) := by
  intro γ g
  simp only [th, row_rational_matrix_mul]
  exact (rowEquiv γ).tsum_eq (fun ξ : NZ => Φ (Ad3.R.row ξ.1 g))

theorem continuous_row (ξ : Fin 2 → ℚ) : Continuous (Ad3.R.row ξ) :=
  Continuous.matrix_vecMul continuous_const Units.continuous_val

theorem measurable_th {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (hΦ : Continuous Φ) : Measurable (th Φ) :=
  Measurable.tsum fun ξ : NZ => (hΦ.comp (continuous_row ξ.1)).measurable

theorem real_id {u w σ : ℝ} (hu : 0 < u) (hw : 0 < w) :
    (u * w ^ 2) ^ σ * u⁻¹ = u ^ (σ - 1) * w ^ (2 * σ) := by
  rw [Real.mul_rpow hu.le (by positivity), Real.rpow_sub_one hu.ne', div_eq_mul_inv]
  have : (w ^ 2) ^ σ = w ^ (2 * σ) := by
    rw [← Real.rpow_natCast w 2, ← Real.rpow_mul hw.le]; norm_num
  rw [this]; ring

theorem point_bound {H : G2 → ℂ} (hH : Aut H) {M : ℕ} {Cd : ℝ}
    (hCd : ∀ x (a : Jd) (κ : KA), ‖H (uni2 x * dg2 a 1 * κ.1)‖ ≤ Cd * min 1 (md a)⁻¹ ^ M)
    (σ : ℝ) (x : 𝔸[ℚ]) (a z : Jd) (κ : KA) (P : ℝ≥0∞) :
    (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * P * ENNReal.ofReal (md a)⁻¹ ≤
      (ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (σ - 1))) *
        (P * ENNReal.ofReal (md z ^ (2 * σ))) := by
  have hu := md_pos a
  have hw := md_pos z
  have hm : 0 ≤ min 1 (md a)⁻¹ ^ M := by positivity
  have hE : ‖H (pt x a z κ.1)‖ₑ ≤ ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M) := by
    rw [pt_eq, hH.cen, ← ENNReal.ofReal_mul' hm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hCd x a κ)
  have e1 : ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ) * ENNReal.ofReal (md a)⁻¹ =
      ENNReal.ofReal (md a ^ (σ - 1)) * ENNReal.ofReal (md z ^ (2 * σ)) := by
    rw [Dt_pt, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), real_id hu hw]
  have e2 : ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (σ - 1)) =
      ENNReal.ofReal (min 1 (md a)⁻¹ ^ M) * ENNReal.ofReal (md a ^ (σ - 1)) :=
    ENNReal.ofReal_mul hm
  calc (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * P * ENNReal.ofReal (md a)⁻¹
      = ‖H (pt x a z κ.1)‖ₑ * (ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ) * ENNReal.ofReal (md a)⁻¹) * P := by ring
    _ ≤ (ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M)) *
          (ENNReal.ofReal (md a ^ (σ - 1)) * ENNReal.ofReal (md z ^ (2 * σ))) * P := by
        rw [e1]; gcongr
    _ = _ := by rw [e2]; ring

theorem g3 : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3 := by
  intro h2a h2b h3a μ 𝓕 mK 𝓓 hS H hH Φ hΦ σ hσ
  obtain ⟨C, hC⟩ := h2a μ 𝓕 mK 𝓓 hS
  obtain ⟨hΦc, hΦb⟩ := h3a Φ hΦ
  refine ⟨measurable_th hΦc, th_linv Φ, ?_⟩
  haveI := hS.probK
  have hHm : Measurable fun g => ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ) :=
    hH.cont.enorm.measurable.mul ((continuous_Dt.measurable.pow_const σ).ennreal_ofReal)
  have hHl : LInv fun g => ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ) := by
    intro γ g
    simp only [hH.left γ g, Dt_mul, detModulus_rational, one_mul]
  rw [h2b μ 𝓕 mK 𝓓 C hS hC (fun g => ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) (fun r => ‖Φ r‖ₑ)
    hHm hHl hΦc.enorm.measurable]
  obtain ⟨Cd, hCd⟩ := hH.dec ⌈σ⌉₊
  obtain ⟨CB, hCB, hB⟩ := hΦb (2 * σ) (by linarith)
  have hMσ : σ - 1 < (⌈σ⌉₊ : ℝ) := by linarith [Nat.le_ceil σ]
  set A : Jd → ℝ≥0∞ := fun a =>
    ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ ⌈σ⌉₊ * md a ^ (σ - 1)) with hA
  set B : Jd → KA → ℝ≥0∞ := fun z κ => ‖Φ (lrow z κ.1)‖ₑ * ENNReal.ofReal (md z ^ (2 * σ)) with hBdef
  have hIA : ∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ < ∞ := by
    simp only [hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS.finD (σ - 1) ⌈σ⌉₊ (by linarith) hMσ)
  have hBne : ∀ z κ, B z κ ≠ ∞ := fun z κ =>
    ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top
  have hx : ∀ (κ : KA) (z a : Jd), ∫⁻ x in fundamentalSet ℚ,
      (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * ‖Φ (lrow z κ.1)‖ₑ *
        ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ≤ A a * B z κ := by
    intro κ z a
    calc _ ≤ ∫⁻ _ in fundamentalSet ℚ, A a * B z κ ∂adeleMeasure ℚ :=
          lintegral_mono fun x => point_bound hH hCd σ x a z κ _
      _ = A a * B z κ := by
          rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  have ha : ∀ (κ : KA) (z : Jd), ∫⁻ a in 𝓓, ∫⁻ x in fundamentalSet ℚ,
      (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * ‖Φ (lrow z κ.1)‖ₑ *
        ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ∂ideleMeasure ℚ ≤
        (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * B z κ := by
    intro κ z
    calc _ ≤ ∫⁻ a in 𝓓, A a * B z κ ∂ideleMeasure ℚ := lintegral_mono fun a => hx κ z a
      _ = _ := lintegral_mul_const' _ _ (hBne z κ)
  have hz : ∀ κ : KA, ∫⁻ z, ∫⁻ a in 𝓓, ∫⁻ x in fundamentalSet ℚ,
      (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * ‖Φ (lrow z κ.1)‖ₑ *
        ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ≤
        (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * CB := by
    intro κ
    calc _ ≤ ∫⁻ z, (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * B z κ ∂ideleMeasure ℚ :=
          lintegral_mono fun z => ha κ z
      _ = (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * ∫⁻ z, B z κ ∂ideleMeasure ℚ :=
          lintegral_const_mul' _ _ hIA.ne
      _ ≤ _ := by gcongr; exact hB κ
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  calc _ ≤ ∫⁻ _ : KA, (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * CB ∂mK := lintegral_mono hz
    _ = (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * CB := by simp
    _ < ∞ := ENNReal.mul_lt_top hIA hCB

end GlobalTheory.CompanionTheory.BottomRowCoordinates

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProductsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_finite_sum_of_products : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples | exact GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_function_schwartz_bruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | exact GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | (intros; apply GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaarStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_preserves_archimedean_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasureStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_pushforward_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) * S * GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormulaStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheet_density_log_norm_formula : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_domain_open_subgroup_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.near_cusp | exact GlobalTheory.CompanionTheory.RapidDecay.near_cusp | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.near_cusp <;> assumption)
end


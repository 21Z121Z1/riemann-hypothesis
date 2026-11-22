import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupDisintegration
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

theorem leftInvariant_of_section : ∀ {Γ K X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (e : K →* Γ) (_ : Continuous e) [MeasurableSpace X] (ρ : Measure X) [SFinite ρ] (s : X → Γ) (_ : Measurable s) (_ : ρ ≠ 0) (_ : ∀ g : Γ, ∃ a : X → X, Measurable a ∧ Measure.map a ρ = ρ ∧ ∀ᵐ x ∂ρ, ∃ k, g * s x = s (a x) * e k) (_ : ∀ A : Set Γ, IsCompact A → ρ (s ⁻¹' (A * Set.range e)) < ⊤) (μ : Measure Γ) [μ.IsHaarMeasure], ∃ c : ℝ, 0 < c ∧ ∀ F : Γ → ℂ, Continuous F → HasCompactSupport F → (∀ y k, F (y * e k) = F y) → ∫ y, F y ∂μ = c * ∫ x, F (s x) ∂ρ := by
  intro Γ K X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he _ ρ _ s hs hρ hinv hfin μ _
  obtain ⟨m, hmH, hm1⟩ : ∃ m : Measure K, m.IsHaarMeasure ∧ m Set.univ = 1 := by
    refine ⟨Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K), inferInstance, ?_⟩
    have h := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  haveI := hmH
  haveI : IsFiniteMeasure m := ⟨by rw [hm1]; exact ENNReal.one_lt_top⟩
  set φ : X × K → Γ := fun p => s p.1 * e p.2 with hφ_def
  have hφ : Measurable φ := (hs.comp measurable_fst).mul (he.measurable.comp measurable_snd)
  set ν : Measure Γ := Measure.map φ (ρ.prod m) with hν_def
  have key : ∀ (B : Set Γ) (y : Γ) (k : K),
      m ((fun k' => y * e k * e k') ⁻¹' B) = m ((fun k' => y * e k') ⁻¹' B) := by
    intro B y k
    have h : (fun k' => y * e k * e k') ⁻¹' B = (fun k' => k * k') ⁻¹' ((fun k' => y * e k') ⁻¹' B) := by
      ext k'; simp [map_mul, mul_assoc]
    rw [h, measure_preimage_mul]
  have hνapp : ∀ B : Set Γ, MeasurableSet B →
      ν B = ∫⁻ x, m ((fun k => s x * e k) ⁻¹' B) ∂ρ := by
    intro B hB
    rw [hν_def, Measure.map_apply hφ hB, Measure.prod_apply (hφ hB)]
    rfl
  have hmeasψ : ∀ B : Set Γ, MeasurableSet B →
      Measurable (fun x => m ((fun k => s x * e k) ⁻¹' B)) := by
    intro B hB
    exact measurable_measure_prodMk_left (hφ hB)
  haveI : ν.IsMulLeftInvariant := by
    constructor
    intro g
    ext B hB
    rw [Measure.map_apply (measurable_const_mul g) hB, hνapp _ (measurable_const_mul g hB), hνapp B hB]
    obtain ⟨a, ha, hamap, hae⟩ := hinv g
    calc ∫⁻ x, m ((fun k => s x * e k) ⁻¹' ((fun h => g * h) ⁻¹' B)) ∂ρ
        = ∫⁻ x, m ((fun k => s (a x) * e k) ⁻¹' B) ∂ρ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          obtain ⟨k, hk⟩ := hx
          have h1 : (fun k' => s x * e k') ⁻¹' ((fun h => g * h) ⁻¹' B)
              = (fun k' => s (a x) * e k * e k') ⁻¹' B := by
            ext k'
            simp only [Set.mem_preimage]
            rw [← mul_assoc, hk]
          rw [h1, key]
      _ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂(Measure.map a ρ) := by
          rw [lintegral_map (hmeasψ B hB) ha]
      _ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂ρ := by rw [hamap]
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro A hA
    have hsub : φ ⁻¹' A ⊆ (s ⁻¹' (A * Set.range e)) ×ˢ Set.univ := by
      intro p hp
      refine ⟨?_, Set.mem_univ _⟩
      simp only [Set.mem_preimage] at hp ⊢
      exact Set.mem_mul.mpr ⟨s p.1 * e p.2, hp, e (p.2⁻¹), ⟨p.2⁻¹, rfl⟩, by simp [mul_assoc]⟩
    calc ν A = (ρ.prod m) (φ ⁻¹' A) := Measure.map_apply hφ hA.isClosed.measurableSet
      _ ≤ (ρ.prod m) ((s ⁻¹' (A * Set.range e)) ×ˢ Set.univ) := measure_mono hsub
      _ = ρ (s ⁻¹' (A * Set.range e)) * m Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by rw [hm1, mul_one]; exact hfin A hA
  have hνeq := Measure.isMulLeftInvariant_eq_smul ν μ
  set c := ν.haarScalarFactor μ with hc_def
  have hc0 : c ≠ 0 := by
    intro h0
    have h : ν Set.univ = 0 := by rw [hνeq, h0, zero_smul]; rfl
    rw [hνapp _ MeasurableSet.univ] at h
    simp only [Set.preimage_univ, hm1, lintegral_const, one_mul] at h
    exact hρ (Measure.measure_univ_eq_zero.mp h)
  have hcR : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hc0
  refine ⟨(c : ℝ)⁻¹, inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)), ?_⟩
  intro F hF _ hFK
  have h1 : ∫ y, F y ∂ν = ∫ x, F (s x) ∂ρ := by
    rw [hν_def, integral_map hφ.aemeasurable hF.aestronglyMeasurable]
    have h : (fun p : X × K => F (φ p)) = fun p => F (s p.1) := by
      funext p; exact hFK (s p.1) p.2
    have hf := integral_fun_fst (μ := ρ) (ν := m) (fun x => F (s x))
    rw [h, hf, measureReal_def, hm1]
    simp
  have h2 : ∫ y, F y ∂ν = ((c : ℝ) : ℂ) * ∫ y, F y ∂μ := by
    conv_lhs => rw [hνeq]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rw [← h1, h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hcR, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.ConeHaar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.CptSobProof

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Van {V : Type} [Zero V] (R : ℝ) (f : Mat n → V) : Prop := ∀ y ∈ GLs n, R < lg y → f y = 0

theorem isOpen_GLs : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_far (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (R : ℝ) :
    IsOpen {y : Mat n | y ∈ GLs n ∧ R < lg y} := by
  have h := hlg.isOpen_inter_preimage isOpen_GLs (isOpen_Ioi (a := R))
  exact h

section Vanish

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {R : ℝ} {f : Mat n → V}

theorem Van.rd (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (X : Mat n) : Van R (Rd X f) := by
  intro y hy hR
  have he : f =ᶠ[𝓝 y] fun _ => (0 : V) := by
    filter_upwards [(isOpen_far hlg R).mem_nhds ⟨hy, hR⟩] with z hz using h z hz.1 hz.2
  simp [Rd, he.fderiv_eq]

theorem Van.eu (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (a b : Fin n) :
    Van R (Eu s a b f) := by
  intro y hy hR
  have h1 := h.rd hlg (Matrix.single a b 1) y hy hR
  have h2 := h.rd hlg (Matrix.single a b Complex.I) y hy hR
  cases s <;> simp [Eu, h1, h2]

theorem Van.epow (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) (a b : Fin n) :
    Van R (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, h y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => (ih c b).eu hlg s a c y hy hR

theorem Van.gel (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) :
    Van R (gel s m f) := by
  intro y hy hR
  simp only [PositivityTheory.RgBcC.gel, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => h.epow hlg s m a a y hy hR

theorem Van.om (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) : Van R (Om f) := by
  intro y hy hR
  have h1 := h.gel hlg true 2 y hy hR
  have h2 := h.gel hlg false 2 y hy hR
  simp [Om, h1, h2]

theorem Van.rw (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (w : List (Bool × Fin n × Fin n)) :
    Van R (Rw w f) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ih.rd hlg (bs p)

theorem rw_smooth (hC : RCalc) (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hC n).1 V _ ih).1 (bs p)

end Vanish

theorem memLp_of_van [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {R : ℝ} {g : Mat n → V}
    (hK : IsCompact {y : G n | lg y.val ≤ R}) (hc : ContinuousOn g (GLs n)) (hv : Van R g) :
    MemLp (fun y : G n => g y.val) 2 μ := by
  have hcont : Continuous (fun y : G n => g y.val) :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  have hsupp : HasCompactSupport (fun y : G n => g y.val) :=
    HasCompactSupport.intro hK fun y hy => hv y.val (val_mem_GLs y) (not_le.1 hy)
  exact hcont.memLp_of_hasCompactSupport hsupp

theorem cptSob : CptSob := by
  intro n _ _ μ _ V _ _ hL hC f hf hcpt
  obtain ⟨-, -, -, hs, hk, -⟩ := hL n
  obtain ⟨R, hR⟩ := hcpt
  have hv : Van R f := hR
  exact ⟨⟨hf, fun w => memLp_of_van μ (hk R) (rw_smooth hC hf w).continuousOn (hv.rw hs.continuousOn w)⟩,
    R, hv.om hs.continuousOn⟩

end GlobalTheory.CompanionTheory.CptSobProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureCongruenceInvariant
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar

variable {n : ℕ}

theorem posDef_congr_iff (g H : Mat n) (hg : g.det ≠ 0) : (g * H * gᴴ).PosDef ↔ H.PosDef := by
  have hU : IsUnit (star g) := ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)).star
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := H) hU
  rwa [star_star, Matrix.star_eq_conjTranspose] at h

theorem det_congr_re (g H : Mat n) : (g * H * gᴴ).det.re = ‖g.det‖ ^ 2 * H.det.re := by
  have h1 : (g * H * gᴴ).det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) * H.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  rw [h1, Complex.re_ofReal_mul]

theorem coneW_congr (g : Mat n) (v w : Fin n × Fin n → ℝ) (h : hOf w = g * hOf v * gᴴ) :
    coneW n w = ENNReal.ofReal ((‖g.det‖ ^ (2 * n))⁻¹) * coneW n v := by
  unfold coneW
  rw [h, det_congr_re, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (norm_nonneg g.det) (2 * n))),
    mul_pow, ← pow_mul, mul_inv]

theorem map_coneMeas_eq (n : ℕ) (g : Mat n) (hg : g.det ≠ 0)
    (T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ)) (hT : ∀ v, hOf (T v) = g * hOf v * gᴴ)
    (hdet : LinearMap.det T = ‖g.det‖ ^ (2 * n)) : Measure.map T (coneMeas n) = coneMeas n := by
  have hd : 0 < LinearMap.det T := by
    rw [hdet]
    exact pow_pos (norm_pos_iff.2 hg) _
  have hdT : LinearMap.det T ≠ 0 := hd.ne'
  let e : (Fin n × Fin n → ℝ) ≃ᵐ (Fin n × Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero T hdT).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n × Fin n → ℝ) → (Fin n × Fin n → ℝ)) = T := rfl
  have hC : e ⁻¹' cone n = cone n := by
    ext v
    show (hOf (T v)).PosDef ↔ (hOf v).PosDef
    rw [hT v]
    exact posDef_congr_iff g (hOf v) hg
  have hW : ∀ v, coneW n (e v) = ENNReal.ofReal (LinearMap.det T)⁻¹ * coneW n v := by
    intro v
    rw [hdet]
    exact coneW_congr g v (T v) (hT v)
  have hvol : Measure.map e volume
      = ENNReal.ofReal (LinearMap.det T)⁻¹ • (volume : Measure (Fin n × Fin n → ℝ)) := by
    rw [he, Real.map_linearMap_volume_pi_eq_smul_volume_pi hdT, abs_of_pos (inv_pos.2 hd)]
  have hmap : Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n))
      = ENNReal.ofReal (LinearMap.det T)⁻¹ •
        (volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
    conv_lhs => rw [← hC]
    rw [← MeasurableEquiv.restrict_map, hvol, Measure.restrict_smul]
  have ha0 : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hd)).ne'
  have hatop : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← he]
  ext s hs
  rw [MeasurableEquiv.map_apply]
  unfold coneMeas
  rw [withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← ENNReal.mul_right_inj ha0 hatop]
  calc ENNReal.ofReal (LinearMap.det T)⁻¹ *
        ∫⁻ v in e ⁻¹' s, coneW n v ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)
      = ∫⁻ v in e ⁻¹' s, coneW n (e v) ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        simp_rw [hW]
        rw [lintegral_const_mul' _ _ hatop]
    _ = ∫⁻ w in s, coneW n w
          ∂Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = ENNReal.ofReal (LinearMap.det T)⁻¹ *
          ∫⁻ w in s, coneW n w ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.ConeHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureDensityFormula
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

theorem continuous_hOf (n : ℕ) : Continuous (hOf : (Fin n × Fin n → ℝ) → Mat n) := by
  unfold hOf
  fun_prop

theorem isClosed_posSemidef (n : ℕ) : IsClosed {M : Mat n | M.PosSemidef} := by
  have h : {M : Mat n | M.PosSemidef} =
      {M : Mat n | Mᴴ = M} ∩ ⋂ x : Fin n → ℂ, {M : Mat n | 0 ≤ star x ⬝ᵥ M *ᵥ x} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [h]
  refine IsClosed.inter (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id) ?_
  refine isClosed_iInter fun x => isClosed_le continuous_const ?_
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

theorem measurableSet_cone (n : ℕ) : MeasurableSet (cone n) := by
  have h : cone n = (hOf ⁻¹' {M : Mat n | M.PosSemidef}) ∩
      ((fun v => (hOf v : Mat n).det) ⁻¹' {(0 : ℂ)}ᶜ) := by
    ext v
    simp only [cone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun hv => ⟨hv.posSemidef, hv.det_pos.ne'⟩,
      fun hv => (Matrix.PosSemidef.posDef_iff_det_ne_zero hv.1).2 hv.2⟩
  rw [h]
  refine MeasurableSet.inter ((isClosed_posSemidef n).preimage (continuous_hOf n)).measurableSet ?_
  exact (isClosed_singleton.isOpen_compl.preimage
    (continuous_hOf n).matrix_det).measurableSet

theorem measurable_coneW (n : ℕ) : Measurable (coneW n) := by
  have h : Continuous fun v : Fin n × Fin n → ℝ => (hOf v : Mat n).det.re :=
    Complex.continuous_re.comp (continuous_hOf n).matrix_det
  unfold coneW
  exact ((h.measurable.pow_const n).inv).ennreal_ofReal

theorem coneW_toReal_smul (n : ℕ) (f : (Fin n × Fin n → ℝ) → ℂ) {v : Fin n × Fin n → ℝ}
    (hv : v ∈ cone n) : (coneW n v).toReal • f v = f v * ((hOf v).det ^ n)⁻¹ := by
  have hpos : (0 : ℂ) < (hOf v : Mat n).det := Matrix.PosDef.det_pos hv
  obtain ⟨hre, him⟩ := Complex.pos_iff.1 hpos
  have hdet : (hOf v : Mat n).det = (((hOf v : Mat n).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using him.symm)
  have hnn : 0 ≤ ((hOf v : Mat n).det.re ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hre.le n)
  unfold coneW
  rw [ENNReal.toReal_ofReal hnn, Complex.real_smul, mul_comm]
  congr 1
  conv_rhs => rw [hdet]
  push_cast
  rfl

theorem cone_integral : ∀ n : ℕ, (∀ᵐ v ∂(coneMeas n), v ∈ PositivityTheory.RgBcC.cone n) ∧ ∀ f : (Fin n × Fin n → ℝ) → ℂ, ∫ v, f v ∂(coneMeas n) = ∫ v in PositivityTheory.RgBcC.cone n, f v * ((hOf v).det ^ n)⁻¹ := by
  intro n
  refine ⟨?_, fun f => ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cone n))
  · unfold coneMeas
    rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_coneW n).aemeasurable
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top) f]
    exact setIntegral_congr_fun (measurableSet_cone n) fun v hv => coneW_toReal_smul n f hv

end GlobalTheory.CompanionTheory.ConeHaar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiable
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.OneParam

theorem hasDerivAt_zero_of_continuous_oneParam
    {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸)
    (hc : Continuous Φ) (h0 : Φ 0 = 1) (hadd : ∀ s t, Φ (s + t) = Φ s * Φ t) :
    ∃ B, HasDerivAt Φ B 0 := by

  set F : ℝ → 𝔸 := fun x => ∫ s in (0 : ℝ)..x, Φ s with hF
  have hFd : ∀ x, HasDerivAt F (Φ x) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hF0 : F 0 = 0 := by simp [hF]

  have hsl : Filter.Tendsto (slope F 0) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 : 𝔸)) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hFd 0)
    rwa [h0] at this
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, ‖slope F 0 ε - 1‖ < 1 := by
    have := hsl.eventually (Metric.ball_mem_nhds (1 : 𝔸) one_pos)
    filter_upwards [this] with ε hε
    simpa [dist_eq_norm] using hε
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : ε ≠ 0 := hε0

  set u : 𝔸 := slope F 0 ε with hu
  have huF : u = ε⁻¹ • F ε := by
    simp [hu, slope_def_module, hF0]
  have hone : ‖1 - u‖ < 1 := by rwa [norm_sub_rev]
  have huU : IsUnit u := by
    have := (Units.oneSub (1 - u) hone).isUnit
    simpa using this
  obtain ⟨U, hU⟩ := huU
  set v : 𝔸 := ((U⁻¹ : 𝔸ˣ) : 𝔸) with hv
  have huv : u * v = 1 := by rw [← hU, hv]; exact U.mul_inv

  have hmul : ∀ t, Φ t * F ε = F (t + ε) - F t := by
    intro t
    have h1 : Φ t * F ε = ∫ s in (0 : ℝ)..ε, Φ (t + s) := by
      have := (ContinuousLinearMap.mul ℝ 𝔸 (Φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable (μ := volume) 0 ε)
      simp only [ContinuousLinearMap.mul_apply'] at this
      rw [hF]
      simp only [hadd]
      exact this.symm
    have h2 : (∫ s in (0 : ℝ)..ε, Φ (t + s)) = ∫ s in (t + 0)..(t + ε), Φ s :=
      intervalIntegral.integral_comp_add_left (a := 0) (b := ε) Φ t
    rw [h1, h2, add_zero]
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 _) (hc.intervalIntegrable 0 _)).symm

  have hrec : ∀ t, Φ t = (ε⁻¹ • (F (t + ε) - F t)) * v := by
    intro t
    rw [← hmul, ← mul_smul_comm, ← huF, mul_assoc, huv, mul_one]

  have hshift : HasDerivAt (fun t => F (t + ε)) (Φ (0 + ε)) 0 :=
    (hFd (0 + ε)).comp_add_const 0 ε
  have hd : HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v)
      ((ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v) 0 :=
    ((hshift.sub (hFd 0)).const_smul ε⁻¹).mul_const v
  have hfun : Φ = fun t => (ε⁻¹ • (F (t + ε) - F t)) * v := funext hrec
  exact ⟨(ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v, by rw [show HasDerivAt Φ = HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v) from congrArg _ hfun]; exact hd⟩

end GlobalTheory.CompanionTheory.OneParam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvRightEquivariant
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_right_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂) → ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, conv μ E k k' (x * k₂.1) = conv μ E k k' x * E.ρ k₂ := by
  intro _ n _ _ μ _ E k k' _ _ hk' x hx k₂
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹))
      (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])
  have hL : ∀ A, L A = A * E.ρ k₂ := fun A => rfl
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit
      exact this.ne_zero
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  unfold conv
  rw [← hL, ← L.integral_comp_comm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))
  rw [hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem gser_mul_prod : ∀ (n : ℕ) (c : Fin n → ℂ),
    (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  intro n c
  have h := GlobalTheory.Dec.GelfSepProof.gen (fun a => c a + ((n : ℂ) - 1) / 2)
  have e : gser c = PowerSeries.mk (fun k => ∑ a, ∑ b,
      (Formalism.REAL.Amat (fun a => c a + ((n : ℂ) - 1) / 2) ^ k) a b) := rfl
  rw [e]
  simpa only [map_add, map_one] using h

end GlobalTheory.CompanionTheory.WaveMult
end
end


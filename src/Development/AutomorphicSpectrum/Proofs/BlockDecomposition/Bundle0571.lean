import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImPosScaledUpperHalfPlane
section
open Ad3 Ad3.S

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfTheta

open Complex
open scoped Real

theorem sqrt_scale {m : ℕ} (hm : 0 < m) {w : ℂ} (hw : w ≠ 0) :
    ((((m : ℝ) ^ 2 : ℝ) : ℂ) * w) ^ (1 / 2 : ℂ) = (m : ℂ) * w ^ (1 / 2 : ℂ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hne : (((m : ℝ) ^ 2 : ℝ) : ℂ) * w ≠ 0 := mul_ne_zero (by exact_mod_cast hm2.ne') hw
  have hmc : (m : ℂ) = exp ((Real.log m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hm']; simp
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero hw, Complex.log_ofReal_mul hm2 hw, Real.log_pow, hmc,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_class (x : ℕ) (j : ℤ) (m : ℕ) (τ : ℂ) :
    ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ) =
      ee ((x : ℂ) ^ 2 * τ) * jacobiTheta₂_term j (2 * m * x * τ) (2 * m ^ 2 * τ) := by
  unfold ee jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem im_pos_scaled_upper_half_plane {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) : 0 < (2 * (m : ℂ) ^ 2 * τ).im := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : (2 * (m : ℂ) ^ 2 * τ) = (((2 * (m : ℝ) ^ 2 : ℝ)) : ℂ) * τ := by push_cast; ring
  rw [this, Complex.im_ofReal_mul]
  positivity

theorem prefactor {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    ee ((x : ℂ) ^ 2 * τ) * (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) =
      (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (m : ℂ)⁻¹ := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw : (-2 * I * τ) ≠ 0 := by simp [hτ0]
  have e1 : ee ((x : ℂ) ^ 2 * τ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) = 1 := by
    unfold ee
    rw [← Complex.exp_add, Complex.exp_eq_one_iff]
    refine ⟨0, ?_⟩
    field_simp
    ring
  have e2 : (-I * (2 * (m : ℂ) ^ 2 * τ)) = (((m : ℝ) ^ 2 : ℝ) : ℂ) * (-2 * I * τ) := by
    push_cast; ring
  rw [e2, sqrt_scale hm hw, cpow_neg]
  have : ee ((x : ℂ) ^ 2 * τ) * (1 / ((m : ℂ) * (-2 * I * τ) ^ (1 / 2 : ℂ)) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) =
      (ee ((x : ℂ) ^ 2 * τ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) *
        (1 / ((m : ℂ) * (-2 * I * τ) ^ (1 / 2 : ℂ))) := by ring
  rw [this, e1, one_mul, one_div, mul_inv, mul_comm]

theorem class_zero {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    HasSum (fun j : ℤ => ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ))
      ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (m : ℂ)⁻¹ * jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ))) := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := (hasSum_jacobiTheta₂_term (2 * m * x * τ) (im_pos_scaled_upper_half_plane hm hτ)).mul_left (ee ((x : ℂ) ^ 2 * τ))
  have hz : (2 * (m : ℂ) * x * τ) / (2 * (m : ℂ) ^ 2 * τ) = x / m := by field_simp
  rw [jacobiTheta₂_functional_equation, hz] at h
  have hf : (fun j : ℤ => ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ)) =
      fun i : ℤ => ee ((x : ℂ) ^ 2 * τ) * jacobiTheta₂_term i (2 * m * x * τ) (2 * m ^ 2 * τ) :=
    funext fun j => ee_class x j m τ
  rw [hf, ← prefactor hm hτ x]
  have hv : ee ((x : ℂ) ^ 2 * τ) * (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) *
        jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) =
      ee ((x : ℂ) ^ 2 * τ) * (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) *
        jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ))) := by ring
  rw [hv]
  exact h

theorem class_one {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    HasSum (fun j : ℤ => (((x : ℤ) + m * j : ℤ) : ℂ) * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ))
      ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (2 * τ * m)⁻¹ * (m : ℂ)⁻¹ *
        (jacobiTheta₂' (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) / (2 * π * I))) := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have h0 := hasSum_jacobiTheta₂_term (2 * m * x * τ) (im_pos_scaled_upper_half_plane hm hτ)
  have h1 := hasSum_jacobiTheta₂'_term (2 * m * x * τ) (im_pos_scaled_upper_half_plane hm hτ)
  have h := ((h0.mul_left (x : ℂ)).add (h1.mul_left ((m : ℂ) / (2 * π * I)))).mul_left (ee ((x : ℂ) ^ 2 * τ))
  have hz : (2 * (m : ℂ) * x * τ) / (2 * (m : ℂ) ^ 2 * τ) = x / m := by field_simp
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂'_functional_equation, hz] at h
  have hf : (fun j : ℤ => (((x : ℤ) + m * j : ℤ) : ℂ) * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ)) =
      fun i : ℤ => ee ((x : ℂ) ^ 2 * τ) * ((x : ℂ) * jacobiTheta₂_term i (2 * m * x * τ) (2 * m ^ 2 * τ) +
        (m : ℂ) / (2 * π * I) * jacobiTheta₂'_term i (2 * m * x * τ) (2 * m ^ 2 * τ)) := by
    funext j
    rw [ee_class x j m τ]
    simp only [jacobiTheta₂'_term]
    have : (m : ℂ) / (2 * π * I) * (2 * π * I * (j : ℂ)) = m * j := by field_simp
    push_cast
    linear_combination (-(ee ((x : ℂ) ^ 2 * τ) * jacobiTheta₂_term j (2 * m * x * τ) (2 * m ^ 2 * τ))) * this
  rw [hf]
  convert_to HasSum _ (ee ((x : ℂ) ^ 2 * τ) *
      ((x : ℂ) *
          (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) *
            jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ))) +
        (m : ℂ) / (2 * π * I) *
          (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) /
              (2 * (m : ℂ) ^ 2 * τ) *
            (jacobiTheta₂' (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) -
              2 * π * I * (2 * m * x * τ) * jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)))))) using 1
  · have e : ∀ Y : ℂ, (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (2 * τ * m)⁻¹ * (m : ℂ)⁻¹ * Y =
        ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (m : ℂ)⁻¹) * ((2 * τ * m)⁻¹ * Y) := fun Y => by ring
    rw [e, ← prefactor hm hτ x]
    generalize jacobiTheta₂ ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) = A
    generalize jacobiTheta₂' ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) = B
    generalize cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) = E
    generalize (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ)) = P
    generalize ee ((x : ℂ) ^ 2 * τ) = G
    field_simp
    ring
  · exact h

theorem term_dual {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : τ ≠ 0) (x : ℕ) (n : ℤ) :
    jacobiTheta₂_term n ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) =
      ee ((n : ℂ) * x / m) * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold ee jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

theorem class_nu {m ν : ℕ} (hm : 0 < m) (hν : ν ≤ 1) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    ∃ R : ℂ,
      HasSum (fun j : ℤ => (((x : ℤ) + m * j : ℤ) : ℂ) ^ ν * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ))
        ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * m) ^ ν)⁻¹ * (m : ℂ)⁻¹ * R) ∧
      HasSum (fun n : ℤ => (n : ℂ) ^ ν * (ee ((n : ℂ) * x / m) * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))))) R := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hT : 0 < (-1 / (2 * (m : ℂ) ^ 2 * τ)).im := by
    have h := im_pos_scaled_upper_half_plane hm hτ
    have h' : -1 / (2 * (m : ℂ) ^ 2 * τ) = -(2 * (m : ℂ) ^ 2 * τ)⁻¹ := by ring
    rw [h', Complex.neg_im, Complex.inv_im]
    have hne : 2 * (m : ℂ) ^ 2 * τ ≠ 0 := by
      intro h0; rw [h0] at h; simp at h
    have := Complex.normSq_pos.mpr hne
    simp only [neg_div, neg_neg]
    positivity
  interval_cases ν
  · refine ⟨jacobiTheta₂ ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)), ?_, ?_⟩
    · simpa using class_zero hm hτ x
    · have h := hasSum_jacobiTheta₂_term ((x : ℂ) / m) hT
      simpa only [pow_zero, one_mul, term_dual hm hτ0] using h
  · refine ⟨jacobiTheta₂' ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) / (2 * π * I), ?_, ?_⟩
    · simpa using class_one hm hτ x
    · have h := (hasSum_jacobiTheta₂'_term ((x : ℂ) / m) hT).div_const (2 * π * I)
      have hf : (fun n : ℤ => (n : ℂ) ^ 1 * (ee ((n : ℂ) * x / m) * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))))) =
          fun n : ℤ => jacobiTheta₂'_term n ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) / (2 * π * I) := by
        funext n
        rw [jacobiTheta₂'_term, term_dual hm hτ0]
        field_simp
      rw [hf]
      exact h

end GlobalTheory.CompanionTheory.HalfTheta

open GlobalTheory.CompanionTheory.HalfTheta in

theorem GlobalTheory.CompanionTheory.HalfTheta.t1 : T1 := by
  intro Q m ν τ hm hν hτ hQ
  choose R hR₁ hR₂ using fun x : ℕ => class_nu hm hν hτ x
  set C : ℂ := (-2 * Complex.I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * m) ^ ν)⁻¹ * (m : ℂ)⁻¹ with hC
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hper : ∀ (x : ℤ) (j : ℤ), Q (x + m * j) = Q x := by
    intro x j
    have hp : Function.Periodic Q (m : ℤ) := fun y => hQ y
    have := (hp.int_mul j) x
    simpa [mul_comm] using this
  let G : ℤ → ℂ := fun n => Q n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * τ)
  have hslice : ∀ x ∈ Finset.range m,
      HasSum (fun n : ℤ => if n % m = (x : ℤ) then G n else 0) (Q x * (C * R x)) := by
    intro x hx
    have hxm : (x : ℤ) < m := by exact_mod_cast Finset.mem_range.mp hx
    have hinj : Function.Injective (fun j : ℤ => (x : ℤ) + m * j) := by
      intro a b hab
      have : (m : ℤ) * a = m * b := by simpa using hab
      exact mul_left_cancel₀ hmZ.ne' this
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro n hn
      rw [if_neg]
      intro hnx
      exact hn ⟨n / m, by rw [← hnx]; exact Int.emod_add_mul_ediv n m⟩
    · have hmod : ∀ j : ℤ, ((x : ℤ) + m * j) % m = x := by
        intro j
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by positivity) hxm
      have hf : ((fun n : ℤ => if n % m = (x : ℤ) then G n else 0) ∘ fun j : ℤ => (x : ℤ) + m * j) =
          fun j : ℤ => Q x * ((((x : ℤ) + m * j : ℤ) : ℂ) ^ ν * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ)) := by
        funext j
        simp only [Function.comp, hmod j, if_true, G, hper]
        ring
      rw [hf]
      exact (hR₁ x).mul_left _
  have hsum := hasSum_sum hslice
  have hG : (fun n : ℤ => ∑ x ∈ Finset.range m, if n % m = (x : ℤ) then G n else 0) = G := by
    funext n
    have h0 : 0 ≤ n % m := Int.emod_nonneg _ hmZ.ne'
    have h1 : n % m < m := Int.emod_lt_of_pos _ hmZ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
    have hkm : k < m := by omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hk'
      exact absurd (Finset.mem_range.mpr hkm) hk'
  rw [hG] at hsum
  have hth : th Q ν τ = ∑ x ∈ Finset.range m, Q x * (C * R x) := hsum.tsum_eq
  have hdual : HasSum (fun n : ℤ => (∑ x ∈ Finset.range m, Q x * ee (n * x / m)) * (n : ℂ) ^ ν *
      ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ)))) (∑ x ∈ Finset.range m, Q x * R x) := by
    have h := hasSum_sum fun x (_ : x ∈ Finset.range m) => (hR₂ x).mul_left (Q x)
    have hf : (fun n : ℤ => (∑ x ∈ Finset.range m, Q x * ee (n * x / m)) * (n : ℂ) ^ ν *
        ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ)))) =
        fun n : ℤ => ∑ x ∈ Finset.range m, Q x * ((n : ℂ) ^ ν * (ee ((n : ℂ) * x / m) *
          ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))))) := by
      funext n
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hf]
    exact h
  rw [hth, hdual.tsum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnTranslateFd
section
open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology Asymptotics
open scoped MatrixGroups ModularForm Modular ENNReal NNReal Pointwise
open ConjAct
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.CuspHeight

theorem volume_strip_lt_top : volume {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im} < ⊤ := by
  let Φ := Complex.measurableEquivRealProd
  let s : Set (ℝ × ℝ) := Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ioi (1 / 4 : ℝ)
  let gg : ℝ → ℝ≥0∞ := fun y => ((((1 / ‖y‖₊) ^ 2 : ℝ≥0)) : ℝ≥0∞)
  rw [volume_eq_lintegral]
  have hsub : (UpperHalfPlane.coe '' {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im}) ⊆ Φ ⁻¹' s := by
    rintro _ ⟨z, ⟨h1, h2⟩, rfl⟩
    have h3 := abs_le.1 h1
    simp only [Set.mem_preimage, s, Set.mem_prod, Set.mem_Icc, Set.mem_Ioi, Φ,
      Complex.measurableEquivRealProd_apply]
    refine ⟨⟨h3.1, h3.2⟩, ?_⟩
    have : (1 / 2 : ℝ) ≤ (z : ℂ).im := h2
    linarith
  refine (lintegral_mono_set hsub).trans_lt ?_
  have h1 := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Φ.measurableEmbedding (fun p : ℝ × ℝ => gg p.2) s
  have h2 : ∫⁻ a in Φ ⁻¹' s, ((((1 / ‖a.im‖₊) ^ 2 : ℝ≥0)) : ℝ≥0∞) =
      ∫⁻ a in Φ ⁻¹' s, gg (Φ a).2 := rfl
  rw [h2, h1, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h3 : ∫⁻ p : ℝ × ℝ, gg p.2 ∂((volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))).prod
      (volume.restrict (Set.Ioi (1 / 4 : ℝ)))) =
      (∫⁻ _ in Set.Icc (-(1 / 2) : ℝ) (1 / 2), 1) * ∫⁻ y in Set.Ioi (1 / 4 : ℝ), gg y := by
    rw [← lintegral_prod_mul aemeasurable_const (by fun_prop)]
    simp
  rw [h3]
  refine ENNReal.mul_lt_top (by simp) ?_
  have h4 : ∫⁻ y in Set.Ioi (1 / 4 : ℝ), gg y =
      ∫⁻ y in Set.Ioi (1 / 4 : ℝ), ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := lt_trans (by norm_num) hy
    simp only [gg]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [Real.rpow_neg hy0.le]
    simp [abs_of_pos hy0]
  rw [h4]
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).lintegral_lt_top

theorem fd_subset_strip : (𝒟 : Set ℍ) ⊆ {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im} := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

theorem volume_fd_lt_top : volume (𝒟 : Set ℍ) < ⊤ :=
  (measure_mono fd_subset_strip).trans_lt volume_strip_lt_top

theorem measurableSet_fd : MeasurableSet (𝒟 : Set ℍ) := by
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp continuous_re) continuous_const
  exact (h1.inter h2).measurableSet

theorem exists_bound_slash (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    (f : CuspForm Γ k) (σ : SL(2, ℤ)) (m : ℕ) :
    ∃ F : ℝ, ∀ τ ∈ 𝒟, ‖((f : ℍ → ℂ) ∣[k] σ) τ‖ * (1 + τ.im) ^ m ≤ F := by
  have : ((toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv,
      Matrix.SpecialLinearGroup.map_mapGL]
      using! Subgroup.IsArithmetic.conj Γ (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  let h := CuspForm.translate f (σ : GL (Fin 2) ℝ)
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' h
  have hh : ∀ τ, h τ = ((f : ℍ → ℂ) ∣[k] σ) τ := fun τ => rfl
  have hcont : Continuous fun τ : ℍ => ‖h τ‖ * (1 + τ.im) ^ m := by
    have : Continuous (h : ℍ → ℂ) := (ModularFormClass.holo h).continuous
    exact (this.norm).mul ((continuous_const.add UpperHalfPlane.continuous_im).pow m)
  have h1 : (fun t : ℝ => Real.exp (-c * t) * (1 + t) ^ m) =O[atTop] fun _ => (1 : ℝ) := by
    have h2 := ((isLittleO_pow_exp_pos_mul_atTop m hc).isBigO).comp_tendsto
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    have h3 := (isBigO_refl (fun t : ℝ => Real.exp (-c * t)) atTop).mul h2
    refine h3.trans (IsBigO.of_bound (Real.exp c) (Eventually.of_forall fun t => ?_))
    simp only [Function.comp, id, ← Real.exp_add, norm_one, mul_one]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq (by congr 1; ring)
  have h4 : (fun τ : ℍ => ‖h τ‖ * (1 + τ.im) ^ m) =O[atImInfty] fun z : ℍ => z.im ^ (0 : ℝ) := by
    have h5 := hO.norm_left.mul (isBigO_refl (fun τ : ℍ => (1 + τ.im) ^ m) atImInfty)
    refine h5.trans ?_
    simp only [Real.rpow_zero]
    exact h1.comp_tendsto (tendsto_comap (f := fun τ : ℍ => τ.im) (x := atTop))
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont h4
  refine ⟨F, fun τ hτ => ?_⟩
  have := hF τ hτ
  simp only [Real.rpow_zero, mul_one] at this
  rw [← hh]
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

theorem norm_lin_le (p q : ℤ) (τ : ℍ) (h1 : |τ.re| ≤ 1 / 2) (h2 : 0 < τ.im) :
    ‖(p : ℂ) * (τ : ℂ) + q‖ ≤ ((|p| + |q| : ℤ) : ℝ) * (1 + τ.im) := by
  have h3 : ‖(τ : ℂ)‖ ≤ 1 + τ.im := by
    have h4 := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    have h5 : |(τ : ℂ).im| = τ.im := abs_of_pos h2
    have h6 : |(τ : ℂ).re| ≤ 1 / 2 := h1
    linarith
  have h7 : ‖(p : ℂ)‖ = |(p : ℝ)| := by simp
  have h8 : ‖(q : ℂ)‖ = |(q : ℝ)| := by simp
  calc ‖(p : ℂ) * (τ : ℂ) + q‖ ≤ ‖(p : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(q : ℂ)‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ |(p : ℝ)| * (1 + τ.im) + |(q : ℝ)| * (1 + τ.im) := by
        rw [h7, h8]
        have : 0 ≤ |(q : ℝ)| := abs_nonneg _
        have := mul_le_mul_of_nonneg_left h3 (abs_nonneg (p : ℝ))
        nlinarith [τ.im_pos]
    _ = _ := by push_cast; ring

theorem Ht_smul (σ : SL(2, ℤ)) (τ : ℍ) :
    Ht (σ • τ) = (‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ 2 +
      ‖((σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 0 1 : ℤ)‖ ^ 2) / τ.im := by
  have hD : ((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ) ≠ 0 := by
    simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (σ : GL (Fin 2) ℝ) τ
  have hn : ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ≠ 0 := norm_ne_zero_iff.2 hD
  have him : (σ • τ).im = τ.im / ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ModularGroup.denom_apply]
  have hco : ((σ • τ : ℍ) : ℂ) = (((σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 0 1 : ℤ)) /
      (((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have key : ∀ a b y : ℝ, a ≠ 0 → y ≠ 0 → (1 + (b / a) ^ 2) / (y / a ^ 2) = (a ^ 2 + b ^ 2) / y := by
    intro a b y ha hy
    field_simp
  unfold Ht
  rw [hco, norm_div, him]
  exact key _ _ _ hn τ.im_ne_zero

theorem exists_height_bound (σ : SL(2, ℤ)) (k A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ 𝒟,
    ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A ≤ C * (1 + τ.im) ^ (k + 2 * A) := by
  set P : ℝ := ((|σ 1 0| + |σ 1 1| : ℤ) : ℝ) with hP
  set Q : ℝ := ((|σ 0 0| + |σ 0 1| : ℤ) : ℝ) with hQ
  have hP0 : 0 ≤ P := by rw [hP]; exact_mod_cast (by positivity : 0 ≤ |σ 1 0| + |σ 1 1|)
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact_mod_cast (by positivity : 0 ≤ |σ 0 0| + |σ 0 1|)
  refine ⟨P ^ k * (2 * (P ^ 2 + Q ^ 2)) ^ A, by positivity, fun τ hτ => ?_⟩
  have hs := fd_subset_strip hτ
  have hy : 0 < τ.im := τ.im_pos
  have h1 := norm_lin_le (σ 1 0) (σ 1 1) τ hs.1 hy
  have h2 := norm_lin_le (σ 0 0) (σ 0 1) τ hs.1 hy
  have hu : 0 ≤ 1 + τ.im := by linarith
  have h3 : Ht (σ • τ) ≤ 2 * (P ^ 2 + Q ^ 2) * (1 + τ.im) ^ 2 := by
    rw [Ht_smul, div_le_iff₀ hy]
    have h4 : ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ 2 ≤ (P * (1 + τ.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h5 : ‖((σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 0 1 : ℤ)‖ ^ 2 ≤ (Q * (1 + τ.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h6 : 0 ≤ (P ^ 2 + Q ^ 2) * (1 + τ.im) ^ 2 := by positivity
    have h7 : 1 ≤ 2 * τ.im := by linarith [hs.2]
    nlinarith
  have h8 : 0 ≤ Ht (σ • τ) := by
    unfold Ht
    have := (σ • τ).im_pos
    positivity
  calc ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A
      ≤ (P * (1 + τ.im)) ^ k * (2 * (P ^ 2 + Q ^ 2) * (1 + τ.im) ^ 2) ^ A := by
        gcongr
    _ = _ := by
        rw [mul_pow, mul_pow (2 * (P ^ 2 + Q ^ 2)), ← pow_mul, pow_add]
        ring

theorem continuous_Ht : Continuous Ht := by
  unfold Ht
  refine Continuous.div ?_ UpperHalfPlane.continuous_im fun z => z.im_ne_zero
  exact continuous_const.add (continuous_coe.norm.pow 2)

theorem integrableOn_translate_fd : D1 := by
  intro k N _ f σ A
  let φ : ℍ → ℍ := fun z => σ • z
  have hcf : Continuous (f : ℍ → ℂ) := (ModularFormClass.holo f).continuous
  have hG : Continuous fun z : ℍ => ‖f z‖ * Ht z ^ A := hcf.norm.mul (continuous_Ht.pow A)
  have hφ : Continuous φ := continuous_const_smul (σ : GL (Fin 2) ℝ)
  have hmp : MeasurePreserving φ volume volume :=
    measurePreserving_smul (σ : GL (Fin 2) ℝ) volume
  have hemb : MeasurableEmbedding φ := (MeasurableEquiv.smul (σ : GL (Fin 2) ℝ)).measurableEmbedding
  have hpre : φ ⁻¹' {z | σ⁻¹ • z ∈ 𝒟} = 𝒟 := by
    ext z
    simp [φ, -ModularGroup.sl_moeb]
  rw [← hmp.integrableOn_comp_preimage hemb, hpre]
  obtain ⟨F, hF⟩ := exists_bound_slash (k : ℤ) _ f σ (k + 2 * A)
  obtain ⟨C, hC0, hC⟩ := exists_height_bound σ k A
  refine Measure.integrableOn_of_bounded (M := C * F) volume_fd_lt_top.ne
    (hG.comp hφ).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_fd).2 (Eventually.of_forall fun τ hτ => ?_))
  have hsl : ‖f (σ • τ)‖ = ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ *
      ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k := by
    have hD : ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ≠ 0 := by
      refine norm_ne_zero_iff.2 ?_
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (σ : GL (Fin 2) ℝ) τ
    rw [ModularForm.SL_slash_apply, norm_mul, norm_zpow, ModularGroup.denom_apply]
    simp only [zpow_neg, zpow_natCast]
    field_simp
  have h1 := hC τ hτ
  have h2 := hF τ hτ
  have h8 : 0 ≤ Ht (σ • τ) := by
    unfold Ht
    have := (σ • τ).im_pos
    positivity
  have h9 : 0 ≤ ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ := norm_nonneg _
  simp only [Function.comp, φ]
  rw [Real.norm_of_nonneg (by positivity), hsl]
  calc ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * ‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A
      = ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * (‖((σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (σ 1 1 : ℤ)‖ ^ k * Ht (σ • τ) ^ A) := by
        ring
    _ ≤ ‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * (C * (1 + τ.im) ^ (k + 2 * A)) := by gcongr
    _ = C * (‖((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ‖ * (1 + τ.im) ^ (k + 2 * A)) := by ring
    _ ≤ C * F := by gcongr

end GlobalTheory.CompanionTheory.CuspHeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbit
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

theorem isUnder_of_sameOrbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  rintro m n w z z' h ⟨c, hc, rfl⟩ k i
  refine ⟨(h k i).1.trans ?_, fun j hy => ((h k i).2 j hy).trans ?_⟩
  · show z ⟨k, i⟩ ≠ 0 ↔ c k * z ⟨k, i⟩ ≠ 0
    simp [hc k]
  · exact (mul_div_mul_left _ _ (hc k)).symm

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteriaStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_and_maximal_compact_criteria : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  first | exact @GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | exact GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | (intros; apply GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionSurjectiveHoldsStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_projection_surjective_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective <;> assumption)
end


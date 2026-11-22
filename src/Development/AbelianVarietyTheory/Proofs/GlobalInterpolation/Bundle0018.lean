import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficients
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory
namespace PowerSumSecond

lemma norm_sum_pow_mul_prod_le {ι κ : Type*} [Fintype ι] (z : ι → ℂ) (a : κ → ℂ) (B : ℝ)
    (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) :
    ∀ m : ℕ, (∀ k, m ≤ k → k ≤ m + T.card → ‖∑ i, z i ^ k‖ ≤ B) →
      ‖∑ i, z i ^ m * ∏ t ∈ T, (z i - a t)‖ ≤ 2 ^ T.card * B := by
  classical
  induction T using Finset.induction_on with
  | empty => intro m h; simpa using h m le_rfl (by simp)
  | insert t T ht ih =>
    intro m h
    rw [Finset.card_insert_of_notMem ht] at h ⊢
    have ha' : ∀ s ∈ T, ‖a s‖ ≤ 1 := fun s hs => ha s (Finset.mem_insert_of_mem hs)
    have h1 := ih ha' (m + 1) (fun k h1 h2 => h k (by omega) (by omega))
    have h2 := ih ha' m (fun k h1 h2 => h k (by omega) (by omega))
    have e : ∑ i, z i ^ m * ∏ s ∈ insert t T, (z i - a s)
        = ∑ i, z i ^ (m + 1) * ∏ s ∈ T, (z i - a s)
          - a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_insert ht]; ring
    rw [e]
    have h3 : ‖a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ ≤ 2 ^ T.card * B := by
      rw [norm_mul]
      calc _ ≤ 1 * ‖∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ :=
            mul_le_mul_of_nonneg_right (ha t (Finset.mem_insert_self _ _)) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 2 ^ T.card * B + 2 ^ T.card * B := add_le_add h1 h3
      _ = _ := by ring

lemma tendsto_inv_prod {κ : Type*} (a : κ → ℂ) (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) (M : ℕ) :
    Tendsto (fun w : ℂ => (w ^ (M + 1) * ∏ t ∈ T, (w - a t))⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
  have h0 : Tendsto (fun w : ℂ => ‖w‖) (Filter.cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have h1 : Tendsto (fun w : ℂ => ‖w‖⁻¹) (Filter.cocompact ℂ) (𝓝 0) := h0.inv_tendsto_atTop
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [h0.eventually_ge_atTop 2] with w hw
  rw [norm_inv, norm_mul, norm_pow, norm_prod]
  have hp : 1 ≤ ∏ t ∈ T, ‖w - a t‖ := by
    calc (1 : ℝ) = ∏ t ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun t ht => by
        have := norm_sub_norm_le w (a t)
        have := ha t ht
        linarith)
  have hq : ‖w‖ ≤ ‖w‖ ^ (M + 1) := le_self_pow₀ (by linarith) (by omega)
  apply inv_anti₀ (by linarith)
  nlinarith

lemma inv_pow_le_exp (N M : ℕ) (hN : 0 < N) (r : ℝ) (hr : 1 - (N : ℝ) / (2 * (M + N)) ≤ r) :
    1 ≤ r ^ M * Real.exp 1 ^ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  set u : ℝ := N / (2 * M + N) with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : (1 - (N : ℝ) / (2 * (M + N))) * (u + 1) = 1 := by
    rw [hu]; field_simp; ring
  have h2 : 1 ≤ r * Real.exp u := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc (1 : ℝ) = _ := h1.symm
      _ ≤ _ := mul_le_mul hr (Real.add_one_le_exp u) (by linarith) (hs.trans hr)
  have hr0 : 0 ≤ r := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    exact hs.trans hr
  have h3 : Real.exp u ^ M ≤ Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    rw [hu, mul_one, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hM' hN'.le]
  calc (1 : ℝ) ≤ (r * Real.exp u) ^ M := one_le_pow₀ h2
    _ = r ^ M * Real.exp u ^ M := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

lemma core (N M : ℕ) (z : Fin N → ℂ) (i₁ : Fin N) (h1 : ‖z i₁‖ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (B : ℝ) (hB : ∀ k, M + 1 ≤ k → k ≤ M + N → ‖∑ i, z i ^ k‖ ≤ B) :
    ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N ≤ B := by
  classical
  have hN : 0 < N := i₁.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (M + 1) le_rfl (by omega))
  set δ : ℝ := N / (2 * (M + N)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.exists_prod_abs_sub_ge_on_segment N (fun i => ‖z i‖) (1 - δ) δ hδ0
  have hr0 : 0 < r := by linarith
  have hr1' : r ≤ 1 := by linarith
  set D : ℝ := (δ / (2 * Real.exp 1)) ^ N with hD
  have hD0 : 0 < D := by positivity
  have hne : ∀ i, r ≠ ‖z i‖ := by
    intro i hi
    have : ∏ i, |r - ‖z i‖| = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    linarith
  set S : Finset (Fin N) := Finset.univ.filter (fun i => r < ‖z i‖) with hS
  have hmemS : ∀ i, i ∈ S ↔ r < ‖z i‖ := by simp [hS]
  have hmemT : ∀ i ∈ Sᶜ, ‖z i‖ < r := by
    intro i hi
    rw [Finset.mem_compl, hmemS, not_lt] at hi
    exact lt_of_le_of_ne hi (hne i).symm
  have hi₁ : i₁ ∈ S := by
    rw [hmemS]; exact lt_of_le_of_ne (h1 ▸ hr1') (hne i₁)
  set e : Fin S.card ≃ S := S.equivFin.symm with he
  set f : ℂ → ℂ := fun w => ∏ t ∈ Sᶜ, (w - z t) with hf
  have hfne : ∀ w : ℂ, r ≤ ‖w‖ → w ^ (M + 1) * f w ≠ 0 := by
    intro w hw
    refine mul_ne_zero (pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun t ht h => ?_)
    · rintro rfl; simp at hw; linarith
    · have := hmemT t ht
      rw [sub_eq_zero] at h
      rw [h] at hw; linarith
  set G : ℝ := (r ^ (M + 1) * D)⁻¹ with hG
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_interpolation_exterior_small_coeffs S.card (fun j => z (e j))
    (fun w => (w ^ (M + 1) * f w)⁻¹) r G hr0 hr1'
    (fun j => ⟨(hmemS _).1 (e j).2, hz _⟩)
    (by
      refine DifferentiableOn.inv ?_ (fun w hw => hfne w hw)
      refine Differentiable.differentiableOn ?_
      simp only [hf]
      fun_prop)
    (tendsto_inv_prod z Sᶜ (fun t _ => hz t) M)
    (by
      intro w hw
      have e1 : ∏ j, (w - z (e j)) = ∏ t ∈ S, (w - z t) := by
        rw [Equiv.prod_comp e (fun s : S => w - z s), Finset.prod_coe_sort S (fun t => w - z t)]
      have e2 : D ≤ ‖∏ t ∈ S, (w - z t)‖ * ‖f w‖ := by
        rw [← norm_mul, hf]
        simp only
        rw [Finset.prod_mul_prod_compl, norm_prod]
        refine hr3.trans (Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_)
        rw [← hw]; exact abs_norm_sub_norm_le _ _
      have e3 : 0 < ‖f w‖ := norm_pos_iff.2 (right_ne_zero_of_mul (hfne w hw.ge))
      rw [e1, norm_inv, norm_mul, norm_pow, hw, hG, inv_mul_eq_div, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < r ^ (M + 1) := by positivity
      nlinarith)
  have key : (S.card : ℂ) = ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i) := by
    have e1 : ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i)
        = ∑ i, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, ← Finset.sum_add_sum_compl S]
    have e2 : ∑ i ∈ Sᶜ, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : f (z i) = 0 := Finset.prod_eq_zero hi (sub_self _)
      simp [this]
    have e3 : (S.card : ℂ) = ∑ i ∈ S, (1 : ℂ) := by simp
    rw [e2, add_zero]
    refine e3.trans ?_
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hc1 (e.symm ⟨i, hi⟩)
    simp only [Equiv.apply_symm_apply] at this
    rw [this, mul_inv_cancel₀ (hfne _ ((hmemS i).1 hi).le)]
  have hcard : S.card + Sᶜ.card = N := by simp
  have hl : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 ⟨i₁, hi₁⟩
  have hbound : (1 : ℝ) ≤ 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B) := by
    calc (1 : ℝ) ≤ ‖(S.card : ℂ)‖ := by simpa using hl
      _ ≤ ∑ j, ‖c j‖ * (2 ^ Sᶜ.card * B) := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hj := j.2
        exact norm_sum_pow_mul_prod_le z z B Sᶜ (fun t _ => hz t) _
          (fun k h1 h2 => hB k (by omega) (by omega))
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  have h4 : (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ N := by
    calc (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ S.card * 4 ^ Sᶜ.card := by gcongr; norm_num
      _ = 4 ^ N := by rw [← pow_add, hcard]
  have h5 : r ^ M * D ≤ 4 ^ N * B := by
    have : 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B)
        = (4 ^ S.card * 2 ^ Sᶜ.card * B) / (r ^ M * D) := by
      rw [hG]; field_simp; ring
    rw [this, one_le_div (by positivity)] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right h4 hB0)
  have h6 := inv_pow_le_exp N M hN r hr1
  have h7 : ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N = D / (4 ^ N * Real.exp 1 ^ N) := by
    rw [hD, ← mul_pow, ← div_pow, hδ]
    congr 1
    field_simp
    ring
  rw [h7, div_le_iff₀ (by positivity)]
  have h8 : 0 < Real.exp 1 ^ N := by positivity
  calc D ≤ (r ^ M * Real.exp 1 ^ N) * D := le_mul_of_one_le_left hD0.le h6
    _ = (r ^ M * D) * Real.exp 1 ^ N := by ring
    _ ≤ (4 ^ N * B) * Real.exp 1 ^ N := mul_le_mul_of_nonneg_right h5 h8.le
    _ = _ := by ring

end PowerSumSecond

open PowerSumSecond in

theorem powerSum_second_main :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  refine ⟨16 * Real.exp 1 ^ 2, ?_, fun N M z i₀ => ?_⟩
  · have : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ (Real.one_le_exp zero_le_one)
    linarith
  have hN : 0 < N := i₀.pos
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) ⟨i₀, Finset.mem_univ _⟩
  by_cases h0 : z i₁ = 0
  · refine ⟨M + 1, le_rfl, by omega, ?_⟩
    have : ‖z i₀‖ = 0 := le_antisymm (by simpa [h0] using hi₁ i₀ (Finset.mem_univ _)) (norm_nonneg _)
    rw [this, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  have hR : 0 < ‖z i₁‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk, hk'⟩ := Finset.exists_max_image (Finset.Icc (M + 1) (M + N))
    (fun k => ‖∑ i, (z i / z i₁) ^ k‖) ⟨M + 1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  rw [Finset.mem_Icc] at hk
  refine ⟨k, hk.1, hk.2, ?_⟩
  have hc := core N M (fun i => z i / z i₁) i₁ (by simp [h0])
    (fun i => by
      rw [norm_div, div_le_one hR]; exact hi₁ i (Finset.mem_univ _))
    _ (fun j h1 h2 => hk' j (Finset.mem_Icc.2 ⟨h1, h2⟩))
  simp only [div_pow] at hc
  rw [← Finset.sum_div, norm_div, norm_pow, le_div_iff₀ (by positivity), ← div_pow] at hc
  refine le_trans ?_ hc
  gcongr
  exact hi₁ i₀ (Finset.mem_univ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal

namespace GlobalTheory.WeilCriterion

section Modulus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_mul_right_eq_modulus (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) (g : G) :
    ∫⁻ x, f (x * g) ∂μ = (modularCharacterFun g : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by
  rw [← lintegral_map hf (measurable_mul_const g), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl

theorem measure_preimage_mul_right_eq_modulus (μ : Measure G) [μ.IsHaarMeasure] {s : Set G}
    (hs : MeasurableSet s) (g : G) :
    μ ((· * g) ⁻¹' s) = (modularCharacterFun g : ℝ≥0∞) * μ s := by
  rw [← Measure.map_apply (measurable_mul_const g) hs, map_right_mul_eq_modularCharacterFun_smul]
  rfl

theorem exists_measurableSet_pos_finite (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ s : Set G, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ⊤ := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨K, hK.measurableSet, (measure_pos_of_mem_nhds μ hK1).ne', hK.measure_lt_top.ne⟩

theorem measurable_modulus : Measurable fun g : G => (modularCharacterFun g : ℝ≥0∞) := by
  let μ : Measure G := haar
  obtain ⟨s, hs, h0, ht⟩ := exists_measurableSet_pos_finite μ
  have h : (fun g : G => (modularCharacterFun g : ℝ≥0∞)) =
      fun g => μ ((· * g) ⁻¹' s) * (μ s)⁻¹ := by
    funext g
    rw [measure_preimage_mul_right_eq_modulus μ hs, mul_assoc, ENNReal.mul_inv_cancel h0 ht,
      mul_one]
  rw [h]
  exact (measurable_measure_mul_right μ hs).mul_const _

theorem lintegral_modulus_mul_inv (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ := by
  obtain ⟨s, hs, h0, ht⟩ := exists_measurableSet_pos_finite μ
  have h := measure_mul_lintegral_eq μ μ hs f hf
  simp_rw [measure_preimage_mul_right_eq_modulus μ hs] at h
  have h2 : ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * μ s * f x⁻¹ ∂μ =
      μ s * ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ := by
    rw [← lintegral_const_mul' _ _ ht]
    congr 1
    funext x
    ring
  rw [h2] at h
  exact ((ENNReal.mul_right_inj h0 ht).mp h).symm

end Modulus

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]

theorem lintegral_mul_fibre_symm
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {f f' : G → ℝ≥0∞} (hf : Measurable f) (hf' : Measurable f') :
    ∫⁻ g, f g * ∫⁻ h : H, f' (g * h) ∂ν ∂dg = ∫⁻ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g ∂dg := by
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  have e1 : ∀ g, f g * ∫⁻ h : H, f' (g * h) ∂ν = ∫⁻ h : H, f g * f' (g * h) ∂ν := fun g =>
    (lintegral_const_mul _ (by fun_prop)).symm
  have e2 : ∀ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g =
      ∫⁻ h : H, (modularCharacterFun h : ℝ≥0∞) * (f (g * (h : G)⁻¹) * f' g) ∂ν := fun g => by
    rw [← lintegral_mul_const _ (by fun_prop),
      ← lintegral_modulus_mul_inv ν (f := fun h : H => f (g * h) * f' g) (by fun_prop)]
    rfl
  have hm := measurable_modulus (G := H)
  simp_rw [e1, e2]
  have m1 : Measurable fun p : G × H => f p.1 * f' (p.1 * p.2) := by fun_prop
  have m2 : Measurable fun p : G × H => f (p.1 * (p.2 : G)⁻¹) * f' p.1 := by fun_prop
  rw [lintegral_lintegral_swap m1.aemeasurable,
    lintegral_lintegral_swap (μ := dg) ((hm.comp measurable_snd).mul m2).aemeasurable]
  congr 1
  funext h
  rw [lintegral_const_mul _ (by fun_prop), ← hΔ,
    ← lintegral_mul_right_eq_modulus dg (f := fun g => f (g * (h : G)⁻¹) * f' g) (by fun_prop)]
  simp

variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace H]
  [IsTopologicalGroup G] in
theorem measurable_mk : Measurable (QuotientGroup.mk : G → G ⧸ H) :=
  QuotientGroup.continuous_mk.measurable

omit [LocallyCompactSpace G] [T2Space G] [LocallyCompactSpace H] [SecondCountableTopology G] in

theorem fibre_comp_mk_mul (ν : Measure H) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) (F : G ⧸ H → ℝ≥0∞) (g : G) :
    ∫⁻ h : H, F ((g * h : G) : G ⧸ H) * φ (g * h) ∂ν = F (g : G ⧸ H) := by
  simp_rw [QuotientGroup.mk_mul_of_mem g (Subtype.property _)]
  rw [lintegral_const_mul _ (by fun_prop), hφ1, mul_one]

theorem lintegral_comp_mk_mul_indep
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {φ ψ : G → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1)
    (hψ : Measurable ψ) (hψ1 : ∀ g : G, ∫⁻ h : H, ψ (g * h) ∂ν = 1)
    {F : G ⧸ H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (g : G ⧸ H) * φ g ∂dg = ∫⁻ g, F (g : G ⧸ H) * ψ g ∂dg := by
  have h := lintegral_mul_fibre_symm H hΔ dg ν (f := fun g => F (g : G ⧸ H) * φ g)
    ((hF.comp (measurable_mk H)).mul hφ) hψ
  simp_rw [hψ1, mul_one, fibre_comp_mk_mul H ν hφ hφ1] at h
  exact h

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace H]
  [IsTopologicalGroup G] in
theorem map_withDensity_apply (dg : Measure G) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    {A : Set (G ⧸ H)} (hA : MeasurableSet A) :
    (dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H) A =
      ∫⁻ g, A.indicator 1 (g : G ⧸ H) * φ g ∂dg := by
  rw [← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) (measurable_mk H),
    lintegral_withDensity_eq_lintegral_mul _ hφ (g := fun g : G => A.indicator 1 (g : G ⧸ H))
      ((measurable_one.indicator hA).comp (measurable_mk H))]
  simp [mul_comm]

theorem exists_isInvariantRadon (hH : IsClosed (H : Set G))
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h) :
    ∃ μ : Measure (G ⧸ H), IsInvariantRadon H μ := by
  let dg : Measure G := haar
  let ν : Measure H := haar
  obtain ⟨φ, hφ, hφ1, hφK⟩ := GlobalTheory.exists_bruhat_function_closed_subgroup G H hH ν
  refine ⟨(dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H), ?_, ⟨fun K hK => ?_⟩,
    ⟨fun a A hA => ?_⟩⟩
  · intro h0
    have h1 := map_withDensity_apply H dg hφ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.indicator_univ, Pi.one_apply, one_mul] at h1
    have h2 : φ =ᵐ[dg] 0 := (lintegral_eq_zero_iff hφ).mp h1.symm
    have h3 := lintegral_mul_fibre_symm H hΔ dg ν (f := fun _ => 1) measurable_const hφ
    simp_rw [hφ1] at h3
    have h4 : ∫⁻ g, (∫⁻ h : H, (1 : ℝ≥0∞) ∂ν) * φ g ∂dg = 0 := by
      rw [lintegral_const_mul _ hφ, ← h1, mul_zero]
    rw [h4] at h3
    simp only [mul_one, lintegral_const, one_mul, measure_univ_eq_zero] at h3
    exact NeZero.ne dg h3
  · refine hK.measure_lt_top_of_nhdsWithin fun q _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨K₀, hK₀, hg⟩ := exists_compact_mem_nhds g
    obtain ⟨K', C, hK', hC, hb⟩ := hφK K₀ hK₀
    have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K₀) :=
      hK₀.image QuotientGroup.continuous_mk
    haveI : IsClosed (H : Set G) := hH
    refine ⟨(QuotientGroup.mk : G → G ⧸ H) '' K₀,
      mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg), ?_⟩
    rw [map_withDensity_apply H dg hφ hc.measurableSet]
    calc _ ≤ ∫⁻ x, K'.indicator (fun _ => C) x ∂dg := by
          refine lintegral_mono fun x => ?_
          by_cases hx : (x : G ⧸ H) ∈ (QuotientGroup.mk : G → G ⧸ H) '' K₀
          · obtain ⟨k, hk, hkx⟩ := hx
            have hmem : k⁻¹ * x ∈ H := QuotientGroup.eq.mp hkx
            have h := hb k hk ⟨_, hmem⟩
            simp only [mul_inv_cancel_left] at h
            by_cases h0 : φ x = 0
            · simp [h0]
            · rw [Set.indicator_of_mem (h.2 h0), Set.indicator_of_mem (Set.mem_image_of_mem _ hk |> (hkx ▸ ·))]
              simpa using h.1
          · simp [Set.indicator_of_notMem hx]
      _ = C * dg K' := lintegral_indicator_const hK'.measurableSet C
      _ < ⊤ := ENNReal.mul_lt_top hC hK'.measure_lt_top
  · have hA' : MeasurableSet ((fun x : G ⧸ H => a • x) ⁻¹' A) :=
      (continuous_const_smul a).measurable hA
    rw [map_withDensity_apply H dg hφ hA', map_withDensity_apply H dg hφ hA,
      lintegral_comp_mk_mul_indep H hΔ dg ν hφ hφ1 (ψ := fun g => φ (a * g)) (by fun_prop)
        (fun g => by simpa [mul_assoc] using hφ1 (a * g)) (measurable_one.indicator hA'),
      ← lintegral_mul_left_eq_self (fun g : G => A.indicator 1 (g : G ⧸ H) * φ g) a]
    rfl

theorem isInvariantRadon_unique (hH : IsClosed (H : Set G)) (μ μ' : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) (hμ' : IsInvariantRadon H μ') :
    ∃ c : ℝ≥0, 0 < c ∧ μ' = c • μ := by
  let ν : Measure H := haar
  obtain ⟨φ, hφ, hφ1, -⟩ := GlobalTheory.exists_bruhat_function_closed_subgroup G H hH ν
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ := GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ hμ
  obtain ⟨dg', ⟨hdg', hq'⟩, -⟩ := GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ' hμ'
  refine ⟨haarScalarFactor dg' dg, haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  ext A hA
  have hm : Measurable fun g : G => A.indicator (1 : G ⧸ H → ℝ≥0∞) (g : G ⧸ H) * φ g :=
    ((measurable_one.indicator hA).comp (measurable_mk H)).mul hφ
  have hfib : fibreIntegral H ν (fun g : G => A.indicator (1 : G ⧸ H → ℝ≥0∞) (g : G ⧸ H) * φ g) =
      A.indicator 1 := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [fibreIntegral_mk]
    exact fibre_comp_mk_mul H ν hφ hφ1 _ g
  have h1 := (hq _ hm).2
  have h2 := (hq' _ hm).2
  rw [hfib, lintegral_indicator_one hA] at h1 h2
  rw [Measure.smul_apply, ← h1, ← h2]
  conv_lhs => rw [isMulLeftInvariant_eq_smul dg' dg]
  rw [lintegral_smul_measure]

end Main

theorem modulusClause : ModulusClause := by
  intro G _ _ _ _ _ _ H _ _ _ hH hΔ
  borelize G
  exact ⟨exists_isInvariantRadon H hH hΔ, isInvariantRadon_unique H hH⟩

end GlobalTheory.WeilCriterion
end


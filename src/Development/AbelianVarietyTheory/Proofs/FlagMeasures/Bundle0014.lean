import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteAndIsInvInvariantOfContinuousIntegrab
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem sigmaFinite_and_isInvInvariant_of_continuous_integrable :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
      [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : G → ℂ),
      Continuous f → f 1 ≠ 0 → Integrable f μ → SigmaFinite μ ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ μ _ _ f hfc hf1 hfi

  have hf1' : ‖f 1‖ₑ ≠ 0 := enorm_ne_zero.2 hf1
  have hc0 : ‖f 1‖ₑ / 2 ≠ 0 := by simp [hf1']
  have hcT : ‖f 1‖ₑ / 2 ≠ ⊤ := (ENNReal.div_lt_top enorm_ne_top two_ne_zero).ne

  have hUo : IsOpen {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} := isOpen_lt continuous_const hfc.enorm
  have h1U : (1 : G) ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} :=
    ENNReal.half_lt_self hf1' enorm_ne_top

  have hUfin : μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} < ⊤ := by
    calc μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ≤ μ {x : G | ‖f 1‖ₑ / 2 ≤ ‖f x‖ₑ} :=
          measure_mono (Set.setOf_subset_setOf.2 fun _ hx => hx.le)
      _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) / (‖f 1‖ₑ / 2) :=
          meas_ge_le_lintegral_div hfi.aestronglyMeasurable.enorm hc0 hcT
      _ < ⊤ := ENNReal.div_lt_top hfi.2.ne hc0

  have hσ : SigmaFinite μ := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ})
      (fun g => hUo.preimage (continuous_const.mul continuous_id))
    refine Measure.sigmaFinite_of_countable
      (hTc.image fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}) ?_ ?_
    · rintro _ ⟨g, -, rfl⟩
      rw [measure_preimage_mul]
      exact hUfin
    · rw [Set.sUnion_image, hT]
      refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ?_⟩
      show x⁻¹ * x ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}
      rw [inv_mul_cancel]
      exact h1U

  have key : μ.inv = μ := by
    open Pointwise in
    have hVo : IsOpen ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := hUo.inter hUo.inv
    open Pointwise in
    have hV0 : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ 0 :=
      (hVo.measure_pos μ ⟨1, h1U, by simpa using h1U⟩).ne'
    open Pointwise in
    have hVT : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt hUfin).ne
    open Pointwise in
    have hVinv : μ.inv ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) = μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := by
      rw [Measure.inv_apply, Set.inter_inv, inv_inv, Set.inter_comm]
    rw [measure_eq_div_smul μ.inv μ hV0 hVT, hVinv, ENNReal.div_self hV0 hVT, one_smul]
  exact ⟨hσ, ⟨key⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeIntegralsAndCardCompositions
section
open MeasureTheory Finset

namespace GlobalTheory

theorem setIntegral_cube_prod (a : ℕ) (S : Set ℝ) (f : Fin a → ℝ → ℝ) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => S), ∏ i, f i (τ i) = ∏ i, ∫ t in S, f i t := by
  have hμ : (volume : Measure (Fin a → ℝ)).restrict (Set.pi Set.univ (fun _ : Fin a => S)) =
      Measure.pi (fun _ : Fin a => (volume : Measure ℝ).restrict S) := by
    rw [volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin a => (volume : Measure ℝ)) (fun _ => S)
  rw [hμ]
  exact integral_fintype_prod_eq_prod (ι := Fin a) f

theorem setIntegral_Icc_const_div (c lo : ℝ) (h0 : 0 < lo) (h1 : lo ≤ 1 / 2) :
    ∫ t in Set.Icc lo (1 / 2), c / t = c * Real.log (1 / (2 * lo)) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
  have hfun : (fun t : ℝ => c / t) = fun t => c * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos h0 hhalf]
  congr 2
  field_simp

private lemma setIntegral_Ioo_pow_mul_div_eq (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) =
      (c : ℝ) * ((1 / 2 : ℝ) ^ (c * m) / ((c * m : ℕ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, c * m = k + 1 := ⟨c * m - 1, by have := Nat.mul_le_mul hc hm; omega⟩
  have hcongr : Set.EqOn (fun t : ℝ => t ^ (c * m) * ((c : ℝ) / t)) (fun t => (c : ℝ) * t ^ k)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht.1
    simp only
    rw [hk, pow_succ]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    integral_pow, hk]
  push_cast
  ring

theorem setIntegral_Ioo_pow_mul_div (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    0 ≤ ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ∧
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ≤ 1 := by
  rw [setIntegral_Ioo_pow_mul_div_eq c m hm hc]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * m) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (c * m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcm : ((c * m : ℕ) : ℝ) = (c : ℝ) * m := by push_cast; ring
  rw [hcm]
  have hden : (0 : ℝ) < (c : ℝ) * m := by positivity
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_one hden]
  calc (c : ℝ) * (1 / 2 : ℝ) ^ (c * m) ≤ (c : ℝ) * 1 := by gcongr
    _ ≤ (c : ℝ) * m := by gcongr

theorem sum_card_composition_lt (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), composition_card, Nat.add_sub_cancel, pow_succ]
    omega

theorem sizeIntegrals_and_card_compositions :
    (∀ (a : ℕ) (c : Fin a → ℝ) (lo : ℝ), 0 < lo → lo ≤ 1 / 2 → (∀ i, 0 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc lo (1 / 2)), ∏ i, c i / τ i = ∏ i, c i * Real.log (1 / (2 * lo))) ∧ (∀ (a : ℕ) (c : Fin a → ℕ) (m : ℕ), 1 ≤ m → (∀ i, 1 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Ioo (0 : ℝ) (1 / 2)), ∏ i, τ i ^ (c i * m) * ((c i : ℝ) / τ i) ≤ 1) ∧ ∀ q : ℕ, ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  refine ⟨fun a c lo h0 h1 _ => ?_, fun a c m hm hc => ?_, sum_card_composition_lt⟩
  · refine (setIntegral_cube_prod a (Set.Icc lo (1 / 2)) (fun i t => c i / t)).trans ?_
    exact Finset.prod_congr rfl fun i _ => setIntegral_Icc_const_div (c i) lo h0 h1
  · refine (setIntegral_cube_prod a (Set.Ioo (0 : ℝ) (1 / 2))
      (fun i t => t ^ (c i * m) * ((c i : ℝ) / t))).trans_le ?_
    exact Finset.prod_le_one (fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).1)
      fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanInfEq
section
namespace GlobalTheory.SpanInfEq

open NumberField

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (v : V) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ h₁
    · rw [mul_smul]; exact L.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have hb' : algebraMap (RingOfIntegers K) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have : (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x)
        = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ h

theorem span_inf_eq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    obtain ⟨d, hd, h⟩ := exists_smul_mem L hL v
    have hd' : algebraMap (RingOfIntegers K) K d ≠ 0 := by
      intro h0
      exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)
    have hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T := by
      rw [← algebraMap_smul K d v]
      exact T.smul_mem _ hv
    have hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T :=
      Submodule.mem_inf.mpr ⟨h, hdT⟩
    have : v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsLattice K L →
    ∀ (T : Submodule K V),
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (NumberField.RingOfIntegers K) T) : Set V) = T :=
  fun L hL T => span_inf_eq L hL T

end GlobalTheory.SpanInfEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntervalIntegralLeMulIntervalIntegralSq
section
open MeasureTheory

namespace GlobalTheory

theorem sq_intervalIntegral_le_mul_intervalIntegral_sq (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContinuousOn g (Set.Icc 0 s)) :
    (∫ t in (0 : ℝ)..s, g t) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, g t ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hg1 : IntervalIntegrable g volume 0 s := (hg.mono hIcc.subset).intervalIntegrable
  have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 s :=
    ((hg.pow 2).mono hIcc.subset).intervalIntegrable
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0 : ℝ)..s, g t) / s := ⟨_, rfl⟩
  have hcs : c * s = ∫ t in (0 : ℝ)..s, g t := by rw [hc]; exact div_mul_cancel₀ _ hs.ne'
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..s, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hs.le (fun t _ => sq_nonneg _)
  have hexp : (fun t => (g t - c) ^ 2) = fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2 := by
    funext t; ring
  rw [hexp, intervalIntegral.integral_add (hg2.sub (hg1.const_mul (2 * c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hg1.const_mul (2 * c)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have hsq : s * c ^ 2 = c * ∫ t in (0 : ℝ)..s, g t := by rw [← hcs]; ring
  have h1 : c * (∫ t in (0 : ℝ)..s, g t) ≤ ∫ t in (0 : ℝ)..s, g t ^ 2 := by linarith
  have h2 : (∫ t in (0 : ℝ)..s, g t) ^ 2 = s * (c * ∫ t in (0 : ℝ)..s, g t) := by
    rw [← hcs]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hs.le

theorem sobolev_endpoint_one_variable : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H) (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc 0 s) → ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
  intro H _ _ _ φ φ' s hs hd hc
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hφc : ContinuousOn φ (Set.Icc 0 s) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s) := hc.norm
  have hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s :=
    (hn'.mono hIcc.subset).intervalIntegrable
  have hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s :=
    ((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 := by
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint : IntervalIntegrable φ' volume 0 t := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint
    have h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖ := by
      rw [hftc]
      have := norm_sub_le (φ t) (φ t - φ 0)
      rwa [sub_sub_cancel] at this
    have h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i
    have h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖ := by linarith
    nlinarith [norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4),
      sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖),
      sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]
  have hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2) :=
    intervalIntegral.integral_mono_on hs.le intervalIntegrable_const
      ((hA.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 :=
    sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'
  have key : ‖φ 0‖ ^ 2 * s ≤
      2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS hs.le]
  calc ‖φ 0‖ ^ 2 = ‖φ 0‖ ^ 2 * s / s := by field_simp
    _ ≤ (2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2) / s := by
      gcongr
    _ = 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
      field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt
section
open Matrix Finset Real

namespace GlobalTheory

open Matrix Finset Real in

theorem _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by
  have h : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if k < i then j k * j i else 0) + (if i = k then j i ^ 2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne, not_lt.mpr hik.le]
    · subst hik; simp [sq]
    · simp [hik, hik.ne', not_lt.mpr hik.le, mul_comm]
  calc (∑ i, j i) ^ 2 = ∑ i, ∑ k, j i * j k := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ((if i < k then j i * j k else 0) + (if k < i then j k * j i else 0) +
          (if i = k then j i ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h i k
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

open Matrix Finset Real in

theorem _root_.GlobalTheory.dim_unipotent_radical_identities :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by
  intro a j n
  dsimp only
  have key := _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a j
  have hQ : 0 ≤ ∑ i, j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (j i)
  generalize (∑ i, ∑ k, if i < k then j i * j k else 0) = S at key ⊢
  generalize (∑ i, j i ^ 2) = Q at key hQ ⊢
  generalize (∑ i, j i) = J at key ⊢
  refine ⟨by linear_combination (-2) * key, by linear_combination 4 * key, ?_⟩
  nlinarith [key, sq_nonneg J, hQ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarProjectionInfOrthogonalEqOfMemOrthogonal
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem starProjection_inf_orthogonal_eq_sub {n : ℕ}
    (A A' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : A' ≤ A) (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_inf.2
      ⟨A.sub_mem hy (h (A'.starProjection_apply_mem y)), A'.sub_starProjection_mem_orthogonal y⟩
  · intro w hw
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal (A'.starProjection_apply_mem y)
      (Submodule.mem_inf.1 hw).2

theorem starProjection_inf_orthogonal_eq_of_mem_orthogonal {n : ℕ}
    (C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : C' ≤ C) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ C'ᗮ) : (C ⊓ C'ᗮ).starProjection v = C.starProjection v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨C.starProjection_apply_mem v, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (h hz)]
    exact Submodule.inner_right_of_mem_orthogonal hz hv
  · intro w hw
    exact C.starProjection_inner_eq_zero v w (Submodule.mem_inf.1 hw).1

theorem infDist_le_norm_block_mul (n : ℕ)
    (A A' B B' C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (D T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hD : ∀ x, ‖D x‖ = ‖x‖) (hA : A' ≤ A) (hC : C' ≤ C)
    (hB : ∀ x ∈ B, ∀ z ∈ C', ⟪z, D x⟫_ℂ = 0) (hB' : ∀ x ∈ B', ∀ z ∈ C, ⟪z, D x⟫_ℂ = 0)
    (hdim : Module.finrank ℂ C + Module.finrank ℂ B' = n)
    (hT : ∀ y ∈ A, T y ∈ B) (hT' : ∀ y ∈ A', T y ∈ B') (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) :
    Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n))) ≤
      ‖(C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection‖ * ‖y‖ := by
  have hmap : B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Cᗮ := by
    have hinj : Function.Injective (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      intro a b hab
      have h0 : ‖D (a - b)‖ = 0 := by
        rw [map_sub]
        simp only [ContinuousLinearMap.coe_coe] at hab
        rw [hab, sub_self, norm_zero]
      rwa [hD, norm_eq_zero, sub_eq_zero] at h0
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_orthogonal]
      intro z hz
      exact hB' x hx z hz
    · rw [← (Submodule.equivMapOfInjective _ hinj B').finrank_eq]
      symm
      apply Submodule.finrank_add_finrank_orthogonal'
      rw [finrank_euclideanSpace_fin]
      exact hdim
  have hy1 : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y :=
    starProjection_inf_orthogonal_eq_sub A A' hA y hy
  have hy1A : (A ⊓ A'ᗮ).starProjection y ∈ A := by
    rw [hy1]
    exact A.sub_mem hy (hA (A'.starProjection_apply_mem y))
  set w := D (T ((A ⊓ A'ᗮ).starProjection y)) with hw_def
  have hw : w ∈ C'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact hB _ (hT _ hy1A) z hz
  obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B', D b = Cᗮ.starProjection w := by
    have hmem : Cᗮ.starProjection w ∈
        B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [hmap]
      exact Cᗮ.starProjection_apply_mem w
    obtain ⟨b, hb, hbw⟩ := hmem
    exact ⟨b, hb, hbw⟩
  have hmemB' : T (A'.starProjection y) + b ∈ B' :=
    B'.add_mem (hT' _ (A'.starProjection_apply_mem y)) hb
  calc Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n)))
      ≤ dist (T y) (T (A'.starProjection y) + b) := Metric.infDist_le_dist_of_mem hmemB'
    _ = ‖T ((A ⊓ A'ᗮ).starProjection y) - b‖ := by
      rw [dist_eq_norm, hy1, map_sub]
      congr 1
      abel
    _ = ‖w - Cᗮ.starProjection w‖ := by
      rw [← hD, map_sub, hbw]
    _ = ‖C.starProjection w‖ := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    _ = ‖(C ⊓ C'ᗮ).starProjection w‖ := by
      rw [starProjection_inf_orthogonal_eq_of_mem_orthogonal C C' hC w hw]
    _ = ‖((C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection) y‖ := rfl
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFibreTwoIndexEncardBound
section
open scoped ENNReal Classical

namespace GlobalTheory

theorem sum_fibre_two_index_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  intro α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB
  rw [ENNReal.ofReal_sum_of_nonneg hf]
  have h1 : ∑ a ∈ S, ENNReal.ofReal (f a) = ∑ x ∈ R₁, ∑ y ∈ R₂,
      ∑ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y), ENNReal.ofReal (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := xf) (t := R₁) (fun a ha => (hR a ha).1)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (g := yf) (t := R₂)
      (fun a ha => (hR a (Finset.mem_filter.1 ha).1).2.1)]
  rw [h1]
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  have hmem : ∀ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y),
      a ∈ S ∧ xf a = x ∧ yf a = y := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  generalize hS' : (S.filter (fun a => xf a = x)).filter (fun a => yf a = y) = S' at hmem ⊢
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := S'.image Φ)
    (fun a ha => Finset.mem_image_of_mem Φ ha)]
  have hfib : ∀ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ENNReal.ofReal (B₁ x * B₂ y) := by
    intro t ht
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨ha₀S, hx₀, hy₀⟩ := hmem a₀ ha₀
    have hsub : S'.filter (fun a => Φ a = Φ a₀)
        = S.filter (fun b => Φ b = Φ a₀ ∧ xf b = xf a₀ ∧ yf b = yf a₀) := by
      subst hS'
      ext b
      simp only [Finset.mem_filter]
      rw [hx₀, hy₀]
      tauto
    rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun b hb => hf b (Finset.mem_filter.1 hb).1)]
    exact (ENNReal.ofReal_le_ofReal (hB a₀ ha₀S)).trans_eq (by rw [hx₀, hy₀])
  calc ∑ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ∑ t ∈ S'.image Φ, ENNReal.ofReal (B₁ x * B₂ y) := Finset.sum_le_sum hfib
    _ = ((S'.image Φ).card : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      gcongr
      have hsubT : ((S'.image Φ : Finset Θ) : Set Θ) ⊆ Tr x y := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
        obtain ⟨haS, hxa, hya⟩ := hmem a ha
        have h := (hR a haS).2.2
        rw [hxa, hya] at h
        exact h
      have hc := Set.encard_le_encard hsubT
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc

end GlobalTheory
end


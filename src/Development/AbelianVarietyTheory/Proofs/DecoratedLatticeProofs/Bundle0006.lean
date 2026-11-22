import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantPartial
section
noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace GlobalTheory.PartialIntegral

section Real

variable {X A : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem exists_majorant {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (k : ℕ) :
    ∃ b : X → ℝ, Integrable b μ ∧ ∀ x a, ‖a‖ ^ k * ‖F (x, a)‖ ≤ b x := by
  set N : ℕ := Module.finrank ℝ X + 1 with hN
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z : X × A, (1 + ‖z‖) ^ (k + N) * ‖F z‖ ≤ C := by
    have := fun z =>
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + N, 0)) (k := k + N) (n := 0) le_rfl le_rfl F z
    simp only [norm_iteratedFDeriv_zero] at this
    exact ⟨_, this⟩
  refine ⟨fun x => C * (1 + ‖x‖) ^ (-(N : ℝ)), (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C,
    fun x a => ?_⟩
  have hp : 0 < 1 + ‖x‖ := by positivity
  show _ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ))
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  refine le_trans ?_ (hC (x, a))
  have h1 : ‖a‖ ≤ 1 + ‖(x, a)‖ := by have := norm_snd_le (x, a); simp only at this; linarith
  have h2 : 1 + ‖x‖ ≤ 1 + ‖(x, a)‖ := by have := norm_fst_le (x, a); simp only at this; linarith
  rw [pow_add _ k N, mul_right_comm]
  gcongr

theorem continuous_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    Continuous fun x => F (x, a) := F.continuous.comp (continuous_id.prodMk continuous_const)

theorem integrable_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    Integrable (fun x => F (x, a)) μ := by
  obtain ⟨b, hb, h⟩ := exists_majorant μ F 0
  exact hb.mono' (continuous_slice F a).aestronglyMeasurable (Eventually.of_forall fun x => by simpa using h x a)

def dSnd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) : 𝓢(X × A, A →L[ℝ] E) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) ((ContinuousLinearMap.compL ℝ A (X × A) E).flip (ContinuousLinearMap.inr ℝ X A))
    (SchwartzMap.fderivCLM ℝ (X × A) E F)

theorem hasFDerivAt_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (x : X) (a : A) :
    HasFDerivAt (fun a => F (x, a)) (dSnd F (x, a)) a :=
  (F.differentiable (x, a)).hasFDerivAt.comp a (hasFDerivAt_prodMk_right x a)

theorem hasFDerivAt_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    HasFDerivAt (fun a => ∫ x, F (x, a) ∂μ) (∫ x, dSnd F (x, a) ∂μ) a := by
  obtain ⟨b, hb, h⟩ := exists_majorant μ (dSnd F) 0
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun a x => F (x, a)) (F' := fun a x => dSnd F (x, a))
    (s := Set.univ) (bound := b) univ_mem
    (Eventually.of_forall fun a => (continuous_slice F a).aestronglyMeasurable) (integrable_slice μ F a)
    (continuous_slice (dSnd F) a).aestronglyMeasurable
    (Eventually.of_forall fun x a _ => by simpa using h x a) hb
    (Eventually.of_forall fun x a _ => hasFDerivAt_slice F x a)

theorem smooth_decay (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)),
    ContDiff ℝ n (fun a => ∫ x, F (x, a) ∂μ) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ a, ‖a‖ ^ k * ‖iteratedFDeriv ℝ n (fun a => ∫ x, F (x, a) ∂μ) a‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ F
    refine ⟨contDiff_zero.2 (continuous_iff_continuousAt.2 fun a => (hasFDerivAt_integral μ F a).continuousAt), fun k => ?_⟩
    obtain ⟨b, hb, h⟩ := exists_majorant μ F k
    refine ⟨∫ x, b x ∂μ, fun a => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    calc ‖a‖ ^ k * ‖∫ x, F (x, a) ∂μ‖ ≤ ‖a‖ ^ k * ∫ x, ‖F (x, a)‖ ∂μ := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ = ∫ x, ‖a‖ ^ k * ‖F (x, a)‖ ∂μ := (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono ((integrable_slice μ F a).norm.const_mul _) hb fun x => h x a
  | succ n ih =>
    intro E _ _ F
    obtain ⟨h1, h2⟩ := ih _ (dSnd F)
    have e : fderiv ℝ (fun a => ∫ x, F (x, a) ∂μ) = fun a => ∫ x, dSnd F (x, a) ∂μ :=
      funext fun a => (hasFDerivAt_integral μ F a).fderiv
    refine ⟨?_, fun k => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv, e]
      exact ⟨fun a => (hasFDerivAt_integral μ F a).differentiableAt, by simp, h1⟩
    · obtain ⟨C, hC⟩ := h2 k
      exact ⟨C, fun a => by rw [← norm_iteratedFDeriv_fderiv, e]; exact hC a⟩

def intFst {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) : 𝓢(A, E) where
  toFun a := ∫ x, F (x, a) ∂μ
  smooth' := contDiff_infty.2 fun n => (smooth_decay μ n E F).1
  decay' k n := (smooth_decay μ n E F).2 k

theorem schwartz_partial [FiniteDimensional ℝ A] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ))
    (L₁ : X →ₗ[ℝ] V) (L₂ : A →ₗ[ℝ] V) (hL : ∀ x a, L₁ x + L₂ a = 0 → x = 0 ∧ a = 0) :
    (∀ a, Integrable (fun x => f (L₁ x + L₂ a)) μ) ∧ ∃ h : 𝓢(A, ℂ), ∀ a, h a = ∫ x, f (L₁ x + L₂ a) ∂μ := by
  let L : (X × A) →L[ℝ] V := LinearMap.toContinuousLinearMap (L₁.coprod L₂)
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (L₁.coprod L₂)
    (LinearMap.ker_eq_bot'.2 fun z hz => Prod.ext (hL z.1 z.2 hz).1 (hL z.1 z.2 hz).2)
  let F : 𝓢(X × A, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ (g := L) L.hasTemperateGrowth hK f
  exact ⟨fun a => integrable_slice μ F a, intFst μ F, fun a => rfl⟩

end Real

section Finite

variable {Y B W : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [TopologicalSpace B] [T2Space B] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  (ν : Measure Y) [ν.IsAddHaarMeasure]

theorem eventually_invariant {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) :
    ∀ᶠ u in 𝓝 (0 : W), ∀ x, g (x + u) = g x := by
  have h : ∀ᶠ u in 𝓝 (0 : W), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport g
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport g
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem locallyConstant_partial {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g)
    {M₁ : Y → W} {M₂ : B → W} {Q₁ : W → Y} {Q₂ : W → B} (c₁ : Continuous M₁) (c₂ : Continuous M₂) (d₁ : Continuous Q₁)
    (d₂ : Continuous Q₂) (e₁ : ∀ y b, Q₁ (M₁ y + M₂ b) = y) (e₂ : ∀ y b, Q₂ (M₁ y + M₂ b) = b) :
    (∀ b, Integrable (fun y => g (M₁ y + M₂ b)) ν) ∧ IsLocallyConstant (fun b => ∫ y, g (M₁ y + M₂ b) ∂ν) ∧
      HasCompactSupport fun b => ∫ y, g (M₁ y + M₂ b) ∂ν := by
  refine ⟨fun b => ?_, ?_, ?_⟩
  · refine Continuous.integrable_of_hasCompactSupport (h1.continuous.comp (c₁.add continuous_const)) ?_
    refine HasCompactSupport.intro (h2.isCompact.image d₁) fun y hy => ?_
    by_contra h
    exact hy ⟨_, subset_tsupport g h, e₁ y b⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun b => ?_
    have ht : Tendsto (fun b' => M₂ b' - M₂ b) (𝓝 b) (𝓝 0) :=
      (c₂.sub continuous_const).tendsto' b 0 (sub_self _)
    filter_upwards [ht.eventually (eventually_invariant h1 h2)] with b' hb'
    congr 1
    funext y
    rw [← hb' (M₁ y + M₂ b)]
    congr 1
    abel
  · refine HasCompactSupport.intro (h2.isCompact.image d₂) fun b hb => ?_
    have : (fun y => g (M₁ y + M₂ b)) = fun _ => 0 := by
      funext y
      by_contra h
      exact hb ⟨_, subset_tsupport g h, e₂ y b⟩
    rw [this, integral_zero]

end Finite

theorem exists_integral_split {G X Y : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (e : G ≃ₜ+ X × Y) (m : Measure G) [m.IsAddHaarMeasure] (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y)
    [ν.IsAddHaarMeasure] :
    ∃ c : ℂ, ∀ (u : X → ℂ) (v : Y → ℂ), Integrable u μ → Integrable v ν →
      Integrable (fun z => u (e z).1 * v (e z).2) m ∧
        ∫ z, u (e z).1 * v (e z).2 ∂m = c * ((∫ x, u x ∂μ) * ∫ y, v y ∂ν) := by
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  haveI : (m.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  have h := Measure.isAddLeftInvariant_eq_smul (m.map e) (μ.prod ν)
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨((Measure.addHaarScalarFactor (m.map e) (μ.prod ν) : ℝ) : ℂ), fun u v hu hv => ⟨?_, ?_⟩⟩
  · have : Integrable (fun z : X × Y => u z.1 * v z.2) (m.map e) := by
      rw [h]
      exact (hu.mul_prod hv).smul_measure_nnreal
    exact he.integrable_map_iff.1 this
  · rw [← he.integral_map (fun z : X × Y => u z.1 * v z.2)]
    conv_lhs => rw [h]
    rw [integral_smul_nnreal_measure, integral_prod_mul, NNReal.smul_def, Complex.real_smul]

end GlobalTheory.PartialIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValues
section
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.ChainOnto

theorem exists_orthonormal_expansion_of_sesq {C : Type} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ip x y = conj (ip y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re) :
    ∃ (n : ℕ) (b : Fin n → C), (∀ i j, ip (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x, x = ∑ i, ip x (b i) • b i := by
  let cd : InnerProductSpace.Core ℂ C :=
    { inner := fun x y => ip y x
      conj_inner_symm := fun x y => by simp [hsym y x]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        change ip x x = 0 at hx
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup C := @InnerProductSpace.Core.toNormedAddCommGroup ℂ C _ _ _ cd
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ C
  refine ⟨_, b, fun i j => ?_, fun x => ?_⟩
  · have h := orthonormal_iff_ite.mp b.orthonormal j i
    have e : ⟪b j, b i⟫_ℂ = ip (b i) (b j) := rfl
    rw [e] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · have h := b.sum_repr' x
    exact h.symm

theorem value_of_adjoint_of_mem_span : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  intro X W C _ _ _ _ _ ev K ipD ip pet hD hDpos hsym hpos hpet x F l hF hl hF0
  obtain ⟨n, b, hb, hexp⟩ := exists_orthonormal_expansion_of_sesq ip hsym hpos
  let Φ : (Fin n → W) →ₗ[ℂ] (X → ℂ) := ∑ j, (ev (b j)).comp (LinearMap.proj j)
  have hΦ : ∀ u, Φ u = ∑ j, ev (b j) (u j) := by
    intro u; simp [Φ, LinearMap.sum_apply]
  have hspan : Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} ≤
      (Submodule.pi Set.univ (fun _ : Fin n => K)).map Φ := by
    rw [Submodule.span_le]
    rintro G ⟨y, w, hw, rfl⟩
    refine ⟨fun j => ip y (b j) • w, fun j _ => K.smul_mem _ hw, ?_⟩
    rw [hΦ]
    conv_rhs => rw [hexp y]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_smul, LinearMap.smul_apply]
  obtain ⟨u, hu, hFu⟩ := hspan hF
  have huK : ∀ j, u j ∈ K := fun j => hu j (Set.mem_univ j)
  rw [hΦ] at hFu
  have key : ∀ k, ∀ w ∈ K, ipD w (u k) = ip (b k) x * l w := by
    intro k w hw
    have h1 := hl (b k) w hw
    rw [← hFu, hpet] at h1
    simpa only [hb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h1
  have hex : ∃ k, u k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hF0
    rw [← hFu]
    simp [h]
  obtain ⟨k, hk⟩ := hex
  have hkpos := hDpos (u k) hk
  rw [key k (u k) (huK k)] at hkpos
  have ha : ip (b k) x ≠ 0 := by
    intro h; rw [h, zero_mul] at hkpos; simp at hkpos
  have hx : x ≠ 0 := by
    rintro rfl; exact ha (by simp)
  refine ⟨hx, ?_⟩
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = (conj (ip (b k) x))⁻¹ • u k := ⟨_, rfl⟩
  have hw₀K : w₀ ∈ K := hw₀def ▸ K.smul_mem _ (huK k)
  have hw₀ : ∀ w ∈ K, ipD w w₀ = l w := by
    intro w hw
    rw [hw₀def, LinearMap.map_smulₛₗ, key k w hw, map_inv₀, Complex.conj_conj, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hu_eq : ∀ j, u j = conj (ip (b j) x) • w₀ := by
    intro j
    have hdK : u j - conj (ip (b j) x) • w₀ ∈ K := K.sub_mem (huK j) (K.smul_mem _ hw₀K)
    have hd0 : ∀ w ∈ K, ipD w (u j - conj (ip (b j) x) • w₀) = 0 := by
      intro w hw
      rw [map_sub, LinearMap.map_smulₛₗ, key j w hw, hw₀ w hw, Complex.conj_conj, smul_eq_mul, sub_self]
    by_contra hne
    have := hDpos _ (sub_ne_zero.mpr hne)
    rw [hd0 _ hdK] at this
    simp at this
  refine ⟨w₀, hw₀K, ?_⟩
  rw [← hFu]
  have hsum : ∑ j, ev (b j) (u j) = ∑ j, ev (b j) (conj (ip (b j) x) • w₀) :=
    Finset.sum_congr rfl (fun j _ => by rw [hu_eq j])
  rw [hsum]
  conv_rhs => rw [hexp x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [map_smul, LinearMap.smul_apply]
  rw [hsym x (b j)]

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormPowSubPowLtOne
section
namespace GlobalTheory.UltrametricPowerDifference

theorem norm_pow_sub_pow_lt_one {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K)
    (ha : ‖a‖ ≤ (1 : ℝ)) (hb : ‖b‖ ≤ (1 : ℝ)) (hab : ‖a - b‖ < (1 : ℝ)) (n : ℕ) :
    ‖a ^ n - b ^ n‖ < (1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) ih
    · rw [norm_mul, norm_pow]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)) hab

end GlobalTheory.UltrametricPowerDifference
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PosIffLtCard
section
namespace GlobalTheory.PositiveIffLtCard

theorem pos_iff_lt_card {N : ℕ} {e : Fin N → ℤ} (he : Antitone e) (i : Fin N) :
    (0 : ℤ) < e i ↔ (i : ℕ) < Finset.card {j : Fin N | (0 : ℤ) < e j} := by
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le h (he hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro h
    by_contra hn
    have hsub : ({j : Fin N | (0 : ℤ) < e j} : Finset (Fin N)) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hn (lt_of_lt_of_le hj (he (not_lt.mp hji)))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end GlobalTheory.PositiveIffLtCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
section
namespace GlobalTheory.ExpPow

theorem int_eq_zero_of_exp_I_mul (m : ℤ) (h : Complex.exp (Complex.I * m) = 1) : m = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h1 : (m : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  by_contra hm
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hm (by exact_mod_cast h1)
  apply irrational_pi
  refine ⟨(m : ℚ) / (2 * n), ?_⟩
  push_cast
  rw [h1]
  field_simp

theorem exp_I_pow_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul] at h
  have h2 : Complex.exp (Complex.I * (((a : ℤ) - b : ℤ) : ℂ)) = 1 := by
    have : Complex.I * (((a : ℤ) - b : ℤ) : ℂ) = a * Complex.I - b * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  have := int_eq_zero_of_exp_I_mul _ h2
  omega

theorem pow_exp_I_or_inv_injective :
    ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) →
      w ^ a = w ^ b → a = b := by
  rintro a b w (rfl | rfl) h
  · exact exp_I_pow_injective a b h
  · rw [inv_pow, inv_pow, inv_inj] at h
    exact exp_I_pow_injective a b h

end GlobalTheory.ExpPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
section
noncomputable section

open Matrix ValuativeRel

namespace GlobalTheory.PenVol

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem toBlocks_mul_fin_zero (g h : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks_one_fin_zero : (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

def cosStab (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    Subgroup (GL (n ⊕ Fin 0) k) where
  carrier := {g | g ∈ J ∧ ∀ y : n → k,
    (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨J.mul_mem hg hh, fun y => ?_⟩
    rw [show (g * h).val = g.val * h.val from rfl, toBlocks_mul_fin_zero, ← Matrix.mulVec_mulVec, hg', hh']
  one_mem' := ⟨J.one_mem, fun y => by
    rw [show (1 : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨J.inv_mem hg, fun y => ?_⟩
    have e : g.val.toBlocks₁₁ *ᵥ ((g⁻¹ : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← toBlocks_mul_fin_zero, show g.val * (g⁻¹ : GL (n ⊕ Fin 0) k).val = 1 from g.mul_inv,
        toBlocks_one_fin_zero, Matrix.one_mulVec]
    rw [← hg', e]

theorem mem_cosStab {J : Subgroup (GL (n ⊕ Fin 0) k)} {M : Submodule 𝒪[k] (n → k)} {c : (n → k) ⧸ M}
    {g : GL (n ⊕ Fin 0) k} : g ∈ cosStab J M c ↔ g ∈ J ∧ ∀ y : n → k,
      (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c := Iff.rfl

theorem cosStab_le (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    cosStab J M c ≤ J := fun _ h => h.1

end GlobalTheory.PenVol

end
end


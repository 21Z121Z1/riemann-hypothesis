import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountRhoPArithStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

def CountRhoPArithStatement : Prop :=
  ∀ (n T δ dV dW : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T → dW ≤ dV →
    δ * (T + n).choose n ≤ dW → dV ≤ δ * (T + 2 * n + 6).choose n →
    ((dV : ℝ) - dW) ≤ (n : ℝ) * (n + 6) * dV / T

def CountRhoArithStatement : Prop :=
  ∀ (n T δ dV ρ : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T →
    δ * (T - 1).choose n + ρ ≤ dV → dV ≤ δ * (T + 2 * n + 6).choose n →
    (ρ : ℝ) ≤ 22 * (n : ℝ) ^ 2 * dV / T

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix

noncomputable section

theorem det_of_key {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] {R : Type*} [CommRing R]
    (M : Matrix m m R) (κ : m → α) (hκ : Function.Injective κ)
    (h : ∀ i j, κ i < κ j → M i j = 0) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' (fun i => OrderDual.toDual (κ i))
    (fun a b hab => hκ (OrderDual.toDual.injective hab))
  exact Matrix.det_of_upperTriangular (fun i j hij => h i j hij)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev Ix (ι : Type*) (r : ℕ) : Type _ := ι × Fin r × Fin r

def sl (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then w (τ, a, b) else 0

def up (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then 0 else w (τ, a, b)

def lu (w : Ix ι r → ℂ) : Ix ι r → ℂ := fun i => ((1 + sl w i.1) * up w i.1) i.2.1 i.2.2

lemma sl_add (h h' : Ix ι r → ℂ) (τ : ι) : sl (h + h') τ = sl h τ + sl h' τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma up_add (h h' : Ix ι r → ℂ) (τ : ι) : up (h + h') τ = up h τ + up h' τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma sl_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : sl (c • h) τ = c • sl h τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma up_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : up (c • h) τ = c • up h τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def luD (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun h i := (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2
  map_add' h h' := by
    funext i
    simp only [sl_add, up_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' c h := by
    funext i
    simp only [sl_smul, up_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring

def key (e : ι ≃ Fin (Fintype.card ι)) (i : Ix ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.2.1 : ℕ) + i.2.2, toLex ((i.2.1 : ℕ), e i.1))

lemma key_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (key (r := r) e) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : a = a' := Fin.ext h2
  have hb : b = b' := Fin.ext (by omega)
  have hτ : τ = τ' := e.injective h3
  subst ha hb hτ
  rfl

lemma key_le_of (e : ι ≃ Fin (Fintype.card ι)) (τ : ι) {a b a' b' : Fin r} (h1 : (a' : ℕ) + b' ≤ a + b)
    (h2 : (a' : ℕ) ≤ a) : key e (τ, a', b') ≤ key e (τ, a, b) := by
  rw [Prod.Lex.le_iff]
  simp only [key, ofLex_toLex]
  rcases h1.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rcases h2.lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', le_rfl⟩

lemma luD_apply (w h : Ix ι r → ℂ) (i : Ix ι r) :
    luD w h i = ∑ k, sl h i.1 i.2.1 k * up w i.1 k i.2.2 + ∑ k, (1 + sl w i.1) i.2.1 k * up h i.1 k i.2.2 := by
  show (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2 = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]

lemma one_add_sl_zero (w : Ix ι r → ℂ) (τ : ι) {a k : Fin r} (h : a < k) : (1 + sl w τ) a k = 0 := by
  rw [Matrix.add_apply, Matrix.one_apply_ne h.ne]
  simp [sl, not_lt.mpr h.le]

lemma toMatrix_luD_zero (e : ι ≃ Fin (Fintype.card ι)) (w : Ix ι r → ℂ) (i j : Ix ι r)
    (hij : key e i < key e j) : LinearMap.toMatrix' (luD w) i j = 0 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hne : ∀ a' b' : Fin r, (a' : ℕ) + b' ≤ a + b → (a' : ℕ) ≤ a → (τ, a', b') ≠ j := by
    rintro a' b' h1 h2 rfl
    exact absurd (key_le_of e τ h1 h2) (not_le.mpr hij)
  have hs1 : ∀ k : Fin r, sl (Pi.single j (1 : ℂ)) τ a k * up w τ k b = 0 := by
    intro k
    by_cases hka : k < a
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne a k (by omega) le_rfl
        simp [Pi.single_apply, sl, hka, this]
    · simp [Pi.single_apply, sl, hka]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single j (1 : ℂ)) τ k b = 0 := by
    intro k
    by_cases hka : a < k
    · rw [one_add_sl_zero w τ hka, zero_mul]
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne k b (by omega) (by omega)
        simp [Pi.single_apply, up, hbk, this]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp

lemma toMatrix_luD_diag (w : Ix ι r → ℂ) (i : Ix ι r) :
    LinearMap.toMatrix' (luD w) i i = if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hs1 : ∀ k : Fin r, sl (Pi.single (τ, a, b) (1 : ℂ)) τ a k * up w τ k b =
      if k = b then (if b < a then w (τ, b, b) else 0) else 0 := by
    intro k
    by_cases hkb : k = b
    · subst hkb
      by_cases hka : k < a <;> simp [Pi.single_apply, sl, up, hka]
    · simp [Pi.single_apply, sl, hkb]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single (τ, a, b) (1 : ℂ)) τ k b =
      if k = a then (if b < a then 0 else 1) else 0 := by
    intro k
    by_cases hka : k = a
    · subst hka
      by_cases hbk : b < k <;> simp [Pi.single_apply, sl, up, hbk]
    · simp [Pi.single_apply, up, hka]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

theorem det_luD (w : Ix ι r → ℂ) :
    LinearMap.det (luD w) = ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  rw [← LinearMap.det_toMatrix', det_of_key _ (key (r := r) (Fintype.equivFin ι))
    (key_injective _) (fun i j h => toMatrix_luD_zero _ w i j h)]
  exact Finset.prod_congr rfl fun i _ => toMatrix_luD_diag w i

def luD' (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →L[ℝ] (Ix ι r → ℂ) :=
  LinearMap.toContinuousLinearMap ((luD w).restrictScalars ℝ)

lemma hasFDerivAt_entry1 (w : Ix ι r → ℂ) (τ : ι) (a k : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => (1 + sl v τ) a k)
      (if k < a then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, a, k) else 0) w := by
  by_cases hk : k < a
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun v => (1 : Matrix (Fin r) (Fin r) ℂ) a k + v (τ, a, k) := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact (hasFDerivAt_apply (𝕜 := ℝ) (τ, a, k) w).const_add _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) a k := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact hasFDerivAt_const _ _

lemma hasFDerivAt_entry2 (w : Ix ι r → ℂ) (τ : ι) (k b : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => up v τ k b)
      (if b < k then 0 else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, k, b)) w := by
  by_cases hk : b < k
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun _ => (0 : ℂ) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_const _ _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun v => v (τ, k, b) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_apply (𝕜 := ℝ) (τ, k, b) w

theorem hasFDerivAt_lu (w : Ix ι r → ℂ) : HasFDerivAt lu (luD' w) w := by
  rw [hasFDerivAt_pi']
  rintro ⟨τ, a, b⟩
  have hf : (fun v : Ix ι r → ℂ => lu v (τ, a, b)) =
      fun v => ∑ k, (1 + sl v τ) a k * up v τ k b := by
    funext v
    simp only [lu, Matrix.mul_apply]
  rw [hf]
  have hd := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (hasFDerivAt_entry1 w τ a k).mul (hasFDerivAt_entry2 w τ k b))
  convert hd using 1
  · funext v
    simp only [Finset.sum_apply, Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply]
    change luD w h (τ, a, b) = _
    rw [luD_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hka : k < a <;> by_cases hbk : b < k <;> simp [hka, hbk, sl, up] <;> ring

theorem det_luD' (w : Ix ι r → ℂ) :
    (luD' w).det = Complex.normSq (∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1) := by
  rw [← det_luD w, ← Algebra.norm_complex_apply]
  show LinearMap.det ((luD w).restrictScalars ℝ) = _
  exact LinearMap.det_restrictScalars

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfG
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

theorem amgm {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by
  have h : 0 ≤ (x - k * y) ^ 2 / k := by positivity
  have e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2 := by
    field_simp
    ring
  linarith

theorem I_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : α → ℝ} {g u : α → ℂ}
    {w : α → ℝ≥0∞} {q : ℝ} (hk : ∀ᵐ a ∂μ, 0 < k a) (hw : ∀ᵐ a ∂μ, w a < ⊤) (hq1 : q < 1)
    (hq0 : 0 ≤ q) (hkm : AEMeasurable k μ) (hgm : AEMeasurable g μ) (hum : AEMeasurable u μ)
    (hwm : AEMeasurable w μ)
    (hI : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ < ⊤)
    (hJ : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ ≤
      ENNReal.ofReal q * ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ)
    (h0 : ∫ a, ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ) ∂μ = 0) :
    ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = 0 := by
  have hWm : AEMeasurable (fun a => (w a).toReal) μ := hwm.ennreal_toReal
  have hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    (hkm.mul (hgm.norm.pow_const 2)).mul hWm
  have hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ((hum.norm.pow_const 2).div hkm).mul hWm
  have hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg
  have hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]
  have hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]
  rw [hA] at hI hJ ⊢
  rw [hB] at hJ
  have hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤ :=
    lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  have hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    ⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩
  have hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩
  have hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable
  have hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable
  have hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    ((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul
      (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable
  have hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤
      (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 := by
    filter_upwards [hk] with a ha
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 := amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha
    have hW0 : 0 ≤ (w a).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  have hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ :=
    (hF2i.add hF1i).div_const 2
  have hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    Integrable.mono' hbdi hPm hPbd
  have hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ := hF1i.ofReal
  have hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) =
      fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ) := by
    funext a
    rw [sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero] at h0
  have hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := integral_nonneg_of_ae hF1nn
  have hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤
      ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
    calc ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ
        = ‖((∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hn]
      _ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]
      _ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ :=
          integral_mono_ae hPi.norm hbdi hPbd
      _ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
          rw [integral_div, integral_add hF2i hF1i]
  have hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := by
    rw [hint1, hint2]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0] at this
  have hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) hn]
  rw [hint1] at hz
  exact ((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

open MvPolynomial

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} [Fintype ι]
  {K : Type*} [CommSemiring K] (σ : K →+* ℂ)

theorem hasFDerivAt_mv (q : MvPolynomial ι K) {h : V → ι → ℂ} {z0 : V} {Dh : ι → V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) :
    HasFDerivAt (fun z => eval₂ σ (h z) q) (∑ i, eval₂ σ (h z0) (pderiv i q) • Dh i) z0 := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const (σ a) z0
  | add p q hp hq =>
    simp only [eval₂_add, map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X]
    refine (hp.mul (hh i)).congr_fderiv ?_
    simp only [Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, eval₂_X, add_smul,
      Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [pderiv_X_self]
    · intro b _ hb
      classical
      rw [pderiv_X]
      simp [hb.symm]
    · simp

def xTerm {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P : Polynomial (MvPolynomial ι K)) : R :=
  P.sum fun n c => ψ (pderiv i c) * s ^ n

theorem xTerm_add {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P Q : Polynomial (MvPolynomial ι K)) : xTerm ψ s i (P + Q) = xTerm ψ s i P + xTerm ψ s i Q := by
  unfold xTerm
  exact Polynomial.sum_add_index _ _ _ (by simp) (by intros; simp [add_mul])

theorem xTerm_monomial {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (n : ℕ) (c : MvPolynomial ι K) : xTerm ψ s i (Polynomial.monomial n c) = ψ (pderiv i c) * s ^ n := by
  unfold xTerm
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem map_xTerm {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : MvPolynomial ι K →+* R)
    (f : R →+* S) (s : R) (i : ι) (P : Polynomial (MvPolynomial ι K)) :
    f (xTerm ψ s i P) = xTerm (f.comp ψ) (f s) i P := by
  unfold xTerm Polynomial.sum
  simp [map_sum]

theorem hasFDerivAt_eval₂ (P : Polynomial (MvPolynomial ι K)) {h : V → ι → ℂ} {g : V → ℂ} {z0 : V}
    {Dh : ι → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) (hg : HasFDerivAt g Dg z0) :
    HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z))
      ((Polynomial.derivative P).eval₂ (eval₂Hom σ (h z0)) (g z0) • Dg +
        ∑ i, xTerm (eval₂Hom σ (h z0)) (g z0) i P • Dh i) z0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add]
    refine (hp.add hq).congr_fderiv ?_
    simp only [map_add, Polynomial.eval₂_add, xTerm_add, add_smul, Finset.sum_add_distrib]
    abel
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial]
    refine ((hasFDerivAt_mv σ c hh).mul (hg.pow n)).congr_fderiv ?_
    simp only [Polynomial.derivative_monomial, xTerm_monomial, Polynomial.eval₂_monomial, coe_eval₂Hom,
      Finset.smul_sum, smul_smul, map_mul, map_natCast, nsmul_eq_mul]
    congr 1
    · congr 1; ring
    · exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

omit [Fintype ι] in

theorem exists_rel {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {y : ι → Ω}
    (hy : AlgebraicIndependent K y) {a : Ω} (ha : IsAlgebraic (Algebra.adjoin K (Set.range y)) a) :
    ∃ P : Polynomial (MvPolynomial ι K), P.eval₂ (aeval y).toRingHom a = 0 ∧
      (Polynomial.derivative P).eval₂ (aeval y).toRingHom a ≠ 0 := by
  classical
  obtain ⟨q, hq0, hqa⟩ := ha
  let f : Algebra.adjoin K (Set.range y) →+* MvPolynomial ι K := hy.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f := hy.aevalEquiv.symm.injective
  have hcomp : (aeval y).toRingHom.comp f = algebraMap (Algebra.adjoin K (Set.range y)) Ω := by
    ext s
    have := hy.algebraMap_aevalEquiv (hy.aevalEquiv.symm s)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  have hex : ∃ n, ∃ P : Polynomial (MvPolynomial ι K), P ≠ 0 ∧
      P.eval₂ (aeval y).toRingHom a = 0 ∧ P.natDegree = n := by
    refine ⟨_, q.map f, (Polynomial.map_ne_zero_iff hf).mpr hq0, ?_, rfl⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hqa
  obtain ⟨P, hP0, hPa, hPn⟩ := Nat.find_spec hex
  refine ⟨P, hPa, fun hd => ?_⟩
  by_cases hD : Polynomial.derivative P = 0
  · have h0 : P.natDegree = 0 := Polynomial.derivative_eq_zero.mp hD
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.eval₂_C] at hPa
    have hc : P.coeff 0 = 0 := hy (by simpa using hPa)
    apply hP0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]
  · have hne : P.natDegree ≠ 0 := fun h0 => hD (Polynomial.derivative_eq_zero.mpr h0)
    have hlt := Polynomial.natDegree_derivative_lt hne
    rw [hPn] at hlt
    exact Nat.find_min hex hlt ⟨_, hD, hd, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA
end


import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapInt
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk

theorem lint_prod {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, ENNReal.ofReal (f v x) ≤ C v) :
    ∫⁻ w : I → P, ENNReal.ofReal (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint : ∀ v, Integrable (f v) := by
    intro v
    refine ⟨(hm v).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]
    exact lt_of_le_of_lt (hC v) ENNReal.coe_lt_top
  have hnn : ∀ w : I → P, 0 ≤ ∏ v, f v (w v) :=
    fun w => Finset.prod_nonneg fun v _ => hf0 v (w v)
  have hP : Integrable (fun w : I → P => ∏ v, f v (w v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ hnn),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.coe_finset_prod]
  refine Finset.prod_le_prod' fun v _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]
  exact hC v

theorem har1 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) :
    kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
  unfold B1c at hB
  obtain ⟨h1, -, h3, -⟩ := hB
  have hzw := (h1 z w).1
  have hzw' := (h1 z w').1
  have key : kap z w ≤ 8 * kap z w' := by
    nlinarith [h3 z w w', mul_le_mul_of_nonneg_left h hzw]
  calc kap z w ^ e ≤ (8 * kap z w') ^ e := Real.rpow_le_rpow hzw key he
    _ = (8 : ℝ) ^ e * kap z w' ^ e := Real.mul_rpow (by norm_num) hzw'

theorem har2 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') :
    (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
  unfold B1c at hB
  obtain ⟨-, -, -, h4, -⟩ := hB
  have hw : 0 < |w.1.im| := abs_pos.mpr w.2
  have hw' : 0 < |w'.1.im| := abs_pos.mpr w'.2
  have hz : 0 ≤ |z.1.im| := abs_nonneg _
  have hww : |w'.1.im| ≤ 8 * |w.1.im| := by
    nlinarith [h4 w w', mul_le_mul_of_nonneg_right h hw'.le]
  have key : |z.1.im| / |w.1.im| ≤ 8 * (|z.1.im| / |w'.1.im|) := by
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left hww hz]
  calc (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 * (|z.1.im| / |w'.1.im|)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hz hw.le) key (by norm_num)
    _ = (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (div_nonneg hz hw'.le)

theorem meas_abs_im : Measurable fun x : P => |x.1.im| := by
  exact (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable

end UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk.KappaIntegralLemmas in
theorem UpperTheory.Esk.pf_KapInt : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B6 → UpperTheory.Esk.KapInt := by
  intro hA _ hB h6
  unfold KapInt
  intro I _ k hk
  have hσ : SigmaFinite (volume : Measure P) := by
    unfold B1a at hA
    exact hA.1
  haveI := hσ
  have hB' := hB
  unfold B1c at hB'
  obtain ⟨h1, -, -, -, h5, -⟩ := hB'
  unfold B6 at h6
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have ha : ∀ v, 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := fun v => by positivity
  have hA' : ((∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ)
      = ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]
    exact Finset.prod_congr rfl fun v _ => Real.coe_toNNReal _ (ha v)
  refine ⟨∏ v, Cv v, ∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)), fun z => ?_⟩
  have hkm : ∀ v, Measurable (fun t : P => kap (z v) t) := fun v =>
    h5.measurable.comp (measurable_const.prodMk measurable_id)
  have hsplit : ∀ w : X I, Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
      = ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) := by
    intro w
    rw [Finset.prod_mul_distrib]
    rfl
  refine ⟨?_, ?_, ?_, fun w w' hn => ⟨?_, ?_⟩⟩
  · unfold Kap
    exact Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _
  · unfold Kap
    exact lint_prod (fun v t => kap (z v) t ^ ((k v : ℝ) / 2))
      (fun v t => Real.rpow_nonneg (h1 _ _).1 _) (fun v => (hkm v).pow_const _) Cv
      (fun v => (hCv v (z v)).1)
  · simp only [hsplit]
    exact lint_prod
      (fun v t => kap (z v) t ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |t.1.im|) ^ ((1 : ℝ) / 2))
      (fun v t => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
        (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
      (fun v => ((hkm v).pow_const _).mul ((measurable_const.div meas_abs_im).pow_const _)) Cv
      (fun v => (hCv v (z v)).2)
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    unfold Kap
    rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => Real.rpow_nonneg (h1 _ _).1 _) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2)
        ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := e1
      _ ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
      (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 hB (z v) (w v) (w' v) (hn' v)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
        ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2)) *
            ((8 : ℝ) ^ ((1 : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul e1 e2 (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _))
      _ = ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) *
            (kap (z v) (w' v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) := by
        ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapSum
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

theorem UpperTheory.Esk.pf_KapSum : UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD
  obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩
  intro y s hs hy ω' z
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy
  obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hpos : 0 ≤ 1 + D.HtY s y := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) →
      (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y)) := by
    intro n hn
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' →
      ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
    intro w w' hww
    calc ENNReal.ofReal (Kap k z w) ≤ ENNReal.ofReal (A₃ * Kap k z w') :=
          ENNReal.ofReal_le_ofReal (hnear w w' hww).1
      _ = (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hpack := hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃
    (ENNReal.measurable_ofReal.comp hmeas) hA hfin
  refine hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))
  rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y)
      = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  push_cast
  ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfMult
section
noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Esk.ExponentialSlopeDerivatives

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

def A (δ : ℝ) (y : D.Y) : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}

theorem near_smul (hB : B1b) (δ : ℝ) (g : PG F) (z w : D.Xs) :
    Near δ (g • z : D.Xs) (g • w : D.Xs) ↔ Near δ z w := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    rw [Dat.mk_smulX D γ z, Dat.mk_smulX D γ w]
    simp only [Near, Dat.act, hB.2.2.2.1]

theorem mem_conj (hB : B1b) (δ : ℝ) (g γ : PG F) (y : D.Y) :
    g * γ * g⁻¹ ∈ A D δ (g • y) ↔ γ ∈ A D δ y := by
  simp only [A, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, mul_smul, inv_smul_smul,
    smul_left_cancel_iff, near_smul D hB]

theorem A_conj (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    A D δ (g • y) = (fun γ => g * γ * g⁻¹) '' A D δ y := by
  ext γ'
  constructor
  · intro h
    refine ⟨g⁻¹ * γ' * g, (mem_conj D hB δ g _ y).1 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]
    · show g * (g⁻¹ * γ' * g) * g⁻¹ = γ'
      group
  · rintro ⟨γ, hγ, rfl⟩
    exact (mem_conj D hB δ g γ y).2 hγ

theorem conj_inj (g : PG F) : Function.Injective (fun γ : PG F => g * γ * g⁻¹) := by
  intro a b h
  simpa using h

theorem fin_card (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    ((A D δ (g • y)).Finite ↔ (A D δ y).Finite) ∧ (A D δ (g • y)).ncard = (A D δ y).ncard := by
  rw [A_conj D hB δ g y]
  exact ⟨Set.finite_image_iff (conj_inj g).injOn, Set.ncard_image_of_injective _ (conj_inj g)⟩

theorem e01 : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem Ht01 [Fintype I] (z : X I) (x : Gf) : D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

end UpperTheory.Esk.ExponentialSlopeDerivatives

open UpperTheory.Esk UpperTheory.Esk.ExponentialSlopeDerivatives

theorem UpperTheory.Esk.pf_Mult : UpperTheory.Esk.B1b → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult := by
  intro hB hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have hcnt : ∀ x' : Gf, ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
      (A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).Finite ∧
      ((A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|) :=
    fun x' => hD.count ((x' : Gf ⧸ D.H)) δ C c hδ hc
  choose C' hC' using hcnt
  have hapos : ∀ x : Gf, 0 < D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H))) := fun x => hD.pos _ e01 _
  have final : ∀ (N Cx P a H K : ℝ), N ≤ Cx * (1 + P) → 0 ≤ P → P * a = H → 0 < a → 0 ≤ H →
      max Cx 0 * (1 + 1 / a) ≤ K → N ≤ K * (1 + H) := by
    intro N Cx P a H K hN hP hPa ha hH hK
    have hP' : P = H / a := eq_div_of_mul_eq ha.ne' hPa
    have h1 : N ≤ max Cx 0 * (1 + P) :=
      hN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have h2 : 1 + P ≤ (1 + 1 / a) * (1 + H) := by
      rw [hP']
      have h0 : 0 ≤ 1 / a := by positivity
      have he : (1 + 1 / a) * (1 + H) - (1 + H / a) = H + 1 / a := by ring
      linarith
    have hM : 0 ≤ max Cx 0 := le_max_right _ _
    calc N ≤ max Cx 0 * (1 + P) := h1
      _ ≤ max Cx 0 * ((1 + 1 / a) * (1 + H)) := mul_le_mul_of_nonneg_left h2 hM
      _ = (max Cx 0 * (1 + 1 / a)) * (1 + H) := by ring
      _ ≤ K * (1 + H) := mul_le_mul_of_nonneg_right hK (by linarith)
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))), ?_⟩
  intro y s hs hy
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by
    rw [h2 _ e01 γ₀ y, hγ₀]
  have hn : c₀ ≤ D.Ht ![0, 1] ((γ₀ : PG F) • y).2 (D.rep ((γ₀ : PG F) • y).1) := by
    rw [← e1] at hy
    exact hy
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ hn
  have hb11 : b.val 1 1 ≠ 0 := by
    intro h0
    apply b.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F), 1] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb10]
  have hsm : ∀ ω : D.Om, (b : PG F) • ω = (((D.j b * D.rep ω : Gf) : Gf ⧸ D.H) : D.Om) := by
    intro ω
    conv_lhs => rw [← QuotientGroup.out_eq' ω]
    rfl
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) =
      (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    show (b : PG F) • ((γ₀ : PG F) • y).1 = _
    rw [hsm, hbx]
    exact QuotientGroup.eq.2 (by simpa using hh)
  obtain ⟨f1, c1⟩ := fin_card D hB δ (γ₀ : PG F) y
  obtain ⟨f2, c2⟩ := fin_card D hB δ (b : PG F) ((γ₀ : PG F) • y)
  rw [hy''] at f2 c2
  obtain ⟨hfin, hle⟩ := hC' x' _ hsg
  refine ⟨f1.1 (f2.1 hfin), ?_⟩
  have hHt : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) = D.HtY s y := by
    rw [← hy'', h2 _ e01 b _, hvb, h3 _ e01 _ hb11, e1]
  have hP : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs)
      = (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep ((x' : Gf ⧸ D.H))) :=
    Ht01 D (D.act b ((γ₀ : PG F) • y).2) (D.rep ((x' : Gf ⧸ D.H)))
  have hH : 0 ≤ D.HtY s y := by linarith
  show ((A D δ y).ncard : ℝ) ≤ _
  rw [← c1, ← c2]
  exact final _ _ _ _ _ _ hle (Finset.prod_nonneg fun v _ => abs_nonneg _) (hP.symm.trans hHt) (hapos x') hH
    (Finset.single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))))
      (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (one_div_nonneg.2 (hapos x).le))) hx'S)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPack
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

namespace KappaPackingLemmas

variable {F I Gf : Type} [Field F] [Group Gf]

theorem kap_smul (hb : B1b) (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g =>
    rw [Dat.mk_smulX, Dat.mk_smulX]
    exact hb.2.2.2.1 (D.r v g) (a v) (b v)

theorem near_sixteenth (hb : B1b) (hc : B1c) (D : Dat F I Gf) (γ₁ γ : PG F) (z w : D.Xs)
    (h₁ : Near (1 / 2) (γ₁ • z : D.Xs) w) (h : Near (1 / 2) (γ • z : D.Xs) w) :
    Near (1 / 16) z ((γ₁⁻¹ * γ) • z : D.Xs) := by
  intro v
  have e : kap (z v) (((γ₁⁻¹ * γ) • z : D.Xs) v) = kap ((γ₁ • z : D.Xs) v) ((γ • z : D.Xs) v) := by
    rw [← kap_smul hb D γ₁ z ((γ₁⁻¹ * γ) • z) v, smul_smul, mul_inv_cancel_left]
  rw [e]
  have a1 := h₁ v
  have a2 := h v
  have s := (hc.1 ((γ • z : D.Xs) v) (w v)).2.2
  have t := hc.2.2.1 ((γ₁ • z : D.Xs) v) (w v) ((γ • z : D.Xs) v)
  rw [← s] at t
  nlinarith

end KappaPackingLemmas

end UpperTheory.Esk

open UpperTheory.Esk UpperTheory.Esk.KappaPackingLemmas in
theorem UpperTheory.Esk.pf_Pack : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.Pack := by
  intro hb hc hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  have := hcnt
  refine ⟨c⁻¹, ?_⟩
  intro y ω' h A hh hA hfin
  set S0 : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)} with hS0
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞) with hN
  let Sg : {γ : PG F // γ • y.1 = ω'} → Set D.Xs := fun γ => {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm : ∀ γ, MeasurableSet (Sg γ) := fun γ => (hcz (γ.1 • y.2)).1

  have one : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    intro γ
    have hv : (c : ℝ≥0∞) ≤ volume (Sg γ) := (hcz (γ.1 • y.2)).2
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) := by
          rw [mul_comm]; gcongr
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w in Sg γ, h w := lintegral_const_mul _ hh
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_indicator (hSm γ)]

  have cnt : ∀ w : D.Xs, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ N * h w := by
    intro w
    by_cases hT : ∃ γ₁ : {γ : PG F // γ • y.1 = ω'}, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      let f : {γ : PG F // γ • y.1 = ω'} → PG F := fun γ => γ₁.1⁻¹ * γ.1
      have finj : Function.Injective f := fun a b hab => Subtype.ext (mul_left_cancel hab)
      let g : PG F → ℝ≥0∞ := S0.indicator fun _ => h w
      have le1 : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ g (f γ) := by
        intro γ
        by_cases hw : w ∈ Sg γ
        · rw [Set.indicator_of_mem hw]
          have hmem : f γ ∈ S0 := by
            refine ⟨?_, near_sixteenth hb hc D γ₁.1 γ.1 y.2 w hγ₁ hw⟩
            change (γ₁.1⁻¹ * γ.1) • y.1 = y.1
            rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm
          simp [g, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hw]; exact bot_le
      calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ ∑' γ, g (f γ) := ENNReal.tsum_le_tsum le1
        _ ≤ ∑' x, g x := ENNReal.tsum_comp_le_tsum_of_injective finj g
        _ = ∑' x : S0, h w := (tsum_subtype S0 fun _ => h w).symm
        _ = N * h w := by
          have : Fintype S0 := hfin.fintype
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, ← Nat.card_coe_set_eq,
            Nat.card_eq_fintype_card]
    · simp only [not_exists] at hT
      have : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w = 0 := fun γ => Set.indicator_of_notMem (hT γ) _
      simp [this]

  have key : (c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2)
        ≤ ∑' γ : {γ : PG F // γ • y.1 = ω'}, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum one
      _ = A * ∑' γ : {γ : PG F // γ • y.1 = ω'}, ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_mul_left
      _ = A * ∫⁻ w, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w := by
          rw [lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * ∫⁻ w, N * h w := by gcongr with w; exact cnt w
      _ = A * (N * ∫⁻ w, h w) := by rw [lintegral_const_mul _ hh]
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)
      = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)) := by
        rw [ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top]
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by
        rw [ENNReal.coe_inv hc0.ne']; ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.SplitTsum
section
open MeasureTheory

namespace UpperTheory.Esk.CentralTermsContribution

open Classical in
theorem split_tsum {G : Type} (P : G → Prop) (f : G → ℂ) (hf : Summable fun g => ‖f g‖) :
    ∑' g, f g = (∑' g, if P g then f g else 0) + ∑' g, if P g then 0 else f g := by
  have h1 : Summable fun g => if P g then f g else 0 :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  have h2 : Summable fun g => if P g then 0 else f g :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  rw [← Summable.tsum_add h1 h2]
  congr 1; funext g; split_ifs <;> simp

end UpperTheory.Esk.CentralTermsContribution

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_TF : UpperTheory.Esk.E2 → UpperTheory.Esk.Ecut → UpperTheory.Esk.E6 → UpperTheory.Esk.Fell → UpperTheory.Esk.Fhyp → UpperTheory.Esk.TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit : ∀ y, (∑' γ : PG F, D.kk k a γ y) = (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y :=
    fun y => CentralTermsContribution.split_tsum _ _ ((hE2 F I Gf ι D k a hH).1 y)
  have hfun : (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    funext y; rw [hsplit y, smul_add]
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY := by
    have := hi.sub hie
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y, smul_add, add_sub_cancel_left]
  have h0 := hFhyp F I Gf ι D k a hH b hb hih
  rw [htr, ← hge, hfun, integral_add hie hih, h0, add_zero]
end


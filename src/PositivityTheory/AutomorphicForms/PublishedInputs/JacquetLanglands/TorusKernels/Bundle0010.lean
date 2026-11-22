import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0070

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelSeriesConvergesProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I]

theorem ht_e (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap; split_ifs <;> positivity

theorem Kap_nonneg (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem N_pos (z : X I) : 0 < ∏ v, |(z v).1.im| :=
  Finset.prod_pos fun v _ => abs_pos.2 (z v).2

theorem fix_of (γ : PG F) (h : γ.out 1 0 = 0) : Fix ![0, 1] γ := by
  refine ⟨γ.out 1 1, ?_⟩
  ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h]

theorem e_ne : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1

theorem kap_split (k : I → ℕ) (z w : X I) :
    Kap k z w = (Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) *
      ((∏ v, |(w v).1.im|) / ∏ v, |(z v).1.im|) ^ ((1 : ℝ) / 2) := by
  rw [← Finset.prod_div_distrib, ← Real.finsetProd_rpow _ _ (fun v _ => by positivity), mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
  intro v _
  have h1 := abs_pos.2 (z v).2
  have h2 := abs_pos.2 (w v).2
  rw [← Real.mul_rpow (by positivity) (by positivity),
    show |(z v).1.im| / |(w v).1.im| * (|(w v).1.im| / |(z v).1.im|) = 1 by field_simp, Real.one_rpow]

theorem ratio (hE0d : E0d) {ι : Type} [Fintype ι] (D : Dat F I Gf) (hax : D.Ax) (a : ι → Gf) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (y : D.Y) (γ : PG F) (i : ι), ¬ Fix ![0, 1] γ →
      γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H) →
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 ≤ C' * ∏ v, |(y.2 v).1.im| := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := hE0d F I Gf D hax
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  choose Cm hCm using fun i => hax.mul (a i)⁻¹
  refine ⟨∑ i, max (Cm i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun y γ i hγ hi => ?_⟩
  have hγ' : γ.out 1 0 ≠ 0 := fun h => hγ (fix_of γ h)
  have hy : D.HtY ![0, 1] y = (∏ v, |(y.2 v).1.im|) * D.hf ![0, 1] (D.rep y.1) := ht_e D y.2 (D.rep y.1)
  have hgy : D.HtY ![0, 1] (γ • y) =
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1 * a i) := by
    have : γ • y = (((D.rep y.1 * a i : Gf) : Gf ⧸ D.H), γ • y.2) := Prod.ext hi rfl
    rw [this]; exact (h1 _ he _ _).trans (ht_e D _ _)
  have hprod : D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y ≤ 1 := by
    have := h2 _ he γ.out y
    rw [QuotientGroup.out_eq'] at this
    rw [this, mul_comm]
    apply h5
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hγ'
  have hx : 0 < D.hf ![0, 1] (D.rep y.1) := hax.pos _ he _
  have hxa : 0 < D.hf ![0, 1] (D.rep y.1 * a i) := hax.pos _ he _
  have hmul : D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.hf ![0, 1] (D.rep y.1 * a i) := by
    simpa using hCm i _ he (D.rep y.1 * a i)
  have hCm0 : 0 ≤ Cm i := by nlinarith
  have hNg : 0 ≤ ∏ v, |((γ • y.2 : D.Xs) v).1.im| := Finset.prod_nonneg fun v _ => abs_nonneg _
  have hN := (N_pos y.2).le
  have hHt : 0 ≤ D.HtY ![0, 1] y := (h4 _ he y).le
  have hHg : 0 ≤ D.HtY ![0, 1] (γ • y) := (h4 _ he _).le
  have hCi : Cm i ≤ ∑ j, max (Cm j) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (Cm j) 0) (fun j _ => le_max_right (Cm j) 0) (Finset.mem_univ i))
  have e1 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 =
      ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| := by
    rw [sq, hy]; ring
  have e2 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.HtY ![0, 1] (γ • y) := by
    rw [hgy]; nlinarith [mul_le_mul_of_nonneg_left hmul hNg]
  rw [e1]
  calc ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im|
      ≤ (Cm i * D.HtY ![0, 1] (γ • y)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 hHt) hN
    _ = Cm i * (D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y) * ∏ v, |(y.2 v).1.im| := by ring
    _ ≤ Cm i * 1 * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCm0) hN
    _ ≤ (∑ j, max (Cm j) 0) * ∏ v, |(y.2 v).1.im| := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hCi hN

theorem main (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hPack : Pack) (hMult : Mult) (hKI : KapInt)
    {ι : Type} [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ≥0, ∀ y : D.Y, c₀ ≤ D.HtY ![0, 1] y →
      ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤ C := by
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  obtain ⟨-, -, -, ⟨CE, hCE⟩, hTe, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨C', hC'0, hC'⟩ := ratio hE0d D hyp.ax a
  obtain ⟨Cp, hCp⟩ := hPack F I Gf D hyp.ax
  obtain ⟨CM, hCM⟩ := hMult F I Gf D hyp.ax (1 / 16) c₀ (by norm_num) hc₀
  obtain ⟨CK, A, hK⟩ := hKI I k hyp.four
  have hm : ∀ v, Measurable fun w : D.Xs => (w v).1.im := fun v =>
    Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v))
  refine ⟨(Fintype.card ι : ℝ≥0) * Cp * A * CK *
    Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)), fun y hy => ?_⟩
  have hHt : 0 < D.HtY ![0, 1] y := hc₀.trans_le hy
  set Ht := D.HtY ![0, 1] y with hHtdef
  set h : D.Xs → ℝ≥0∞ := fun w => ENNReal.ofReal (Kap k y.2 w * ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2))
    with hhdef
  set K : ℝ := max CE 0 * Real.sqrt C' / Ht with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤
      ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := by
    rintro ⟨γ, hγ⟩
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have : D.kk k a γ y = 0 := by simp [Dat.kk, Dat.kt, h0]
      simp [this]
    obtain ⟨i, hi⟩ := hTe γ y.1 h0
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ) (fun _ _ => bot_le) (Finset.mem_univ i))
    simp only [Set.indicator_of_mem (show γ ∈ {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)]
    rw [hhdef, ← ofReal_norm, ← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have hr := hC' y γ i hγ hi
    have hN := N_pos y.2
    have hsq : ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) ≤ Real.sqrt C' / Ht := by
      rw [← Real.sqrt_eq_rpow]
      have : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im| ≤ C' / Ht ^ 2 := by
        rw [div_le_div_iff₀ hN (by positivity)]; linarith
      calc Real.sqrt ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ≤ Real.sqrt (C' / Ht ^ 2) :=
            Real.sqrt_le_sqrt this
        _ = Real.sqrt C' / Ht := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hHt.le]
    have hX : 0 ≤ Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Kap_nonneg _ _ _) (Finset.prod_nonneg fun v _ => by positivity)
    calc ‖D.kk k a γ y‖ ≤ CE * Kap k y.2 (γ • y.2 : D.Xs) := hCE γ y
      _ ≤ max CE 0 * Kap k y.2 (γ • y.2 : D.Xs) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Kap_nonneg _ _ _)
      _ = max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2)) := by
          congr 1; exact kap_split k y.2 _
      _ ≤ max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            (Real.sqrt C' / Ht)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hX) (le_max_right _ _)
      _ = K * (Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) := by
          rw [hKdef]; ring

  have hmeas : Measurable h :=
    ((hK y.2).1.mul (Finset.measurable_prod _ fun v _ =>
      (measurable_const.div (hm v).abs).pow_const _)).ennreal_ofReal
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' → h w ≤ A * h w' := by
    intro w w' hn
    have := ENNReal.ofReal_le_ofReal ((hK y.2).2.2.2 w w' hn).2
    rwa [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this
  obtain ⟨hfin, hcard⟩ := hCM y ![0, 1] he hy
  have hcard' : ((({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (max CM 0 * (1 + Ht)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hint : ∫⁻ w, h w ≤ CK := (hK y.2).2.2.1
  have hcos : ∀ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ ≤
      ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    calc ∑' γ : {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}, h (γ.1 • y.2)
        ≤ Cp * A * ({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℝ≥0∞) * ∫⁻ w, h w :=
          hCp y _ h A hmeas hA hfin
      _ ≤ Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK := by gcongr
  have hfinal : ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht)) ≤
      ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
    rw [← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 + Ht) / Ht ≤ 1 + 1 / c₀ := by
      have := one_div_le_one_div_of_le hc₀ hy
      rw [add_div, div_self hHt.ne']; linarith
    have h2 : 0 ≤ max CE 0 * Real.sqrt C' * max CM 0 := by positivity
    calc K * (max CM 0 * (1 + Ht)) = max CE 0 * Real.sqrt C' * max CM 0 * ((1 + Ht) / Ht) := by
          rw [hKdef]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  calc ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ
      ≤ ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' γ : PG F, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = ∑ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ := Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ i : ι, ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) :=
        Finset.sum_le_sum fun i _ => hcos i
    _ = (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * (ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
        gcongr
    _ = (((Fintype.card ι : ℝ≥0) * Cp * A * CK *
          Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal]; push_cast; ring

end UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_series_converges_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.E1 := by
  intro _ hE0c hE0d hPack hMult hKI F I Gf ι _ _ _ _ D k a hyp c₀ hc₀
  obtain ⟨C, hC⟩ := KernelSeriesConvergence.main hE0c hE0d hPack hMult hKI D k a hyp c₀ hc₀
  refine ⟨C, fun y s hs hy => ?_⟩
  obtain ⟨-, h2, -, -, -, -, -, -, -, h10, h11⟩ := hE0d F I Gf D hyp.ax
  obtain ⟨-, h2c, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨δ, hδ⟩ := h10 s hs
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := KernelSeriesConvergence.e_ne
  have hy' : c₀ ≤ D.HtY ![0, 1] ((δ : PG F) • y) := by rw [h2 _ he δ y, hδ]; exact hy
  have hfix : ∀ γ : PG F, ¬ Fix s γ ↔ ¬ Fix ![0, 1] (MulAut.conj (δ : PG F) γ) := by
    intro γ
    have := h11 ![0, 1] γ.out δ
    rw [QuotientGroup.out_eq', hδ] at this
    exact not_congr this.symm
  let e : {γ : PG F // ¬ Fix s γ} ≃ {γ : PG F // ¬ Fix ![0, 1] γ} :=
    (MulAut.conj (δ : PG F)).toEquiv.subtypeEquiv hfix
  calc ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ
      = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a (e γ).1 ((δ : PG F) • y)‖ₑ := by
        congr 1; funext γ
        rw [show (e γ).1 = (δ : PG F) * γ.1 * (δ : PG F)⁻¹ from rfl, h2c]
    _ = ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ :=
        e.tsum_eq (fun γ => ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ)
    _ ≤ C := hC _ hy'
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelTraceBoundProof
section
open scoped ENNReal NNReal

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_trace_bound_proof : UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases hγ : y ∈ D.LamF T γ
        · have hnf : γ ∈ {γ : PG F | ¬ Fix s γ} := fun hf => absurd (hγ s hs hf) (not_le.2 hsT)
          rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hnf]
        · rw [Set.indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (le_of_lt (hT.trans hsT))
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormulaProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.MultivariableReproducingLemmas

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem nrm_pos {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem norm_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => hb.2.2.2.2.2.1 (k v) (z v) (w v) (hk v)

theorem cont_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (z : X I) : Continuous (qq k z) := by
  unfold qq
  exact continuous_finsetProd _ fun v _ =>
    (hb.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))

theorem integrable {I : Type} [Fintype I] (hb : B1b) (hK : KapInt) (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C)
    (z : X I) : Integrable (fun w => qq k z w * f w) := by
  obtain ⟨C1, A, h⟩ := hK I k hk
  obtain ⟨hm, hl, -⟩ := h z
  have hKi : Integrable (Kap k z) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ w, ‖Kap k z w‖ₑ = ∫⁻ w, ENNReal.ofReal (Kap k z w) := by
          congr 1; funext w; exact Real.enorm_eq_ofReal (Kap_nonneg k z w)
      _ ≤ C1 := hl
      _ < ⊤ := ENNReal.coe_lt_top
  have hc : 0 ≤ ∏ v, (((k v : ℝ) - 1) / (4 * Real.pi)) := Finset.prod_nonneg fun v _ => by
    have h4 : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    exact div_nonneg (by linarith) (by positivity)
  refine (hKi.const_mul ((∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C / nrm k z)).mono'
    ((cont_qq hb k z).mul hf).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have h1 := norm_qq hb k (fun v => le_trans (by norm_num) (hk v)) z w
  have hn := nrm_pos k z
  rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ hn]
  calc ‖qq k z w‖ * ‖f w‖ * nrm k z = (‖qq k z w‖ * nrm k z) * ‖f w‖ := by ring
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * (‖f w‖ * nrm k w) := by rw [h1]; ring
    _ ≤ (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * C :=
        mul_le_mul_of_nonneg_left (hC w) (mul_nonneg hc (Kap_nonneg k z w))
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C * Kap k z w := by ring

theorem symm_eq (n : ℕ) (p : P × (Fin n → P)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 := by
  funext j
  induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem qq_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (z : X (Fin (n + 1))) (t : P) (w : Fin n → P) :
    qq k z (Fin.cons t w) = q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w := by
  simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem nrm_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (t : P) (w : Fin n → P) :
    nrm k (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k 0 : ℝ) / 2) * nrm (fun j => k j.succ) w := by
  simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem fin_case (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) : ∀ (n : ℕ) (k : Fin n → ℕ), (∀ v, 4 ≤ k v) →
    ∀ f : X (Fin n) → ℂ, SepHol f → ∀ C, (∀ z, ‖f z‖ * nrm k z ≤ C) → ∀ z, ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  intro n
  induction n with
  | zero =>
    intro k hk f hf C hC z
    have hF : (fun w => qq k z w * f w) = fun _ => f z := funext fun w => by
      rw [Subsingleton.elim w z]; simp [qq]
    rw [hF, show (volume : Measure (X (Fin 0))) = Measure.dirac z from Measure.pi_of_empty _ z,
      integral_const]
    simp
  | succ n ih =>
    intro k hk f hf C hC z
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
    have hI := integrable hb hK k hk f hf.1 C hC z
    have hG : Integrable (fun p : P × (Fin n → P) =>
        q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 * f (Fin.cons p.1 p.2))
        ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
      have := (hmp.symm.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2 hI
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply, symm_eq, qq_cons]
    have hin : ∀ w : Fin n → P, ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
        f (Fin.cons t w) = qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
      intro w
      have hol : Hol1 fun t => f (Fin.cons t w) := by
        have h := hf.2 (Fin.cons (z 0) w) 0
        convert h using 3 with t
        funext j
        induction j using Fin.cases <;> simp
      have hbd : ∃ C', ∀ t : P, ‖f (Fin.cons t w)‖ * |t.1.im| ^ ((k 0 : ℝ) / 2) ≤ C' := by
        refine ⟨C / nrm (fun j => k j.succ) w, fun t => ?_⟩
        rw [le_div_iff₀ (nrm_pos _ _), mul_assoc, ← nrm_cons]
        exact hC _
      have h := (h3 (k 0) (hk 0) (fun t => f (Fin.cons t w)) hol hbd (z 0)).2
      calc ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons t w)
          = ∫ t, qq (fun j => k j.succ) (fun j => z j.succ) w * (q1 (k 0) (z 0) t * f (Fin.cons t w)) := by
            congr 1; funext t; ring
        _ = _ := by rw [integral_const_mul, h]
    have hsep : SepHol fun w : X (Fin n) => f (Fin.cons (z 0) w) := by
      refine ⟨hf.1.comp (continuous_pi fun j => ?_), fun w v => ?_⟩
      · induction j using Fin.cases
        · simpa using continuous_const
        · simpa using continuous_apply _
      · have h := hf.2 (Fin.cons (z 0) w) v.succ
        convert h using 3 with t
        funext j
        induction j using Fin.cases with
        | zero => simp [(Fin.succ_ne_zero v).symm]
        | succ j =>
          simp only [Fin.cons_succ, Function.update_apply, Fin.succ_inj]
          split_ifs <;> simp_all
    have hbd : ∀ w : X (Fin n), ‖f (Fin.cons (z 0) w)‖ * nrm (fun j => k j.succ) w ≤
        C / |(z 0).1.im| ^ ((k 0 : ℝ) / 2) := by
      intro w
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (z 0).2) _), mul_assoc, mul_comm (nrm _ _), ← nrm_cons]
      exact hC _
    calc ∫ w, qq k z w * f w
        = ∫ p, (fun w => qq k z w * f w)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p)
            ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
          (hmp.symm.integral_comp' _).symm
      _ = ∫ p : P × (Fin n → P), q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 *
            f (Fin.cons p.1 p.2) ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
          congr 1; funext p; simp only [symm_eq, qq_cons]
      _ = ∫ w : Fin n → P, (∫ t : P, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
            f (Fin.cons t w)) ∂(Measure.pi fun _ : Fin n => (volume : Measure P)) := integral_prod_symm _ hG
      _ = ∫ w : X (Fin n), qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
          congr 1; funext w; exact hin w
      _ = f (Fin.cons (z 0) (fun j => z j.succ)) := ih _ (fun v => hk _) _ hsep _ hbd _
      _ = f z := congrArg f (Fin.cons_self_tail z)

theorem main (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) (I : Type) [Fintype I] (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : SepHol f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C) (z : X I) :
    ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ : ∀ (w : X I) j, φ w j = w (σ.symm j) := by
    intro w j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [MeasurableEquiv.coe_piCongrLeft]
    exact this
  have hmp : MeasurePreserving φ (volume : Measure (X I)) (volume : Measure (X (Fin (Fintype.card I)))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) := by
    refine ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => ?_⟩
    have h := hf.2 (fun i => w' (σ i)) (σ.symm j)
    convert h using 3 with t
    funext i
    simp only [Function.update_apply, Equiv.eq_symm_apply]
    split_ifs <;> rfl
  have hnrm : ∀ w' : X (Fin (Fintype.card I)), nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) := by
    intro w'
    exact Fintype.prod_equiv σ.symm _ _ fun j => by simp
  have hbd : ∀ w' : X (Fin (Fintype.card I)), ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    intro w'; rw [hnrm]; exact hC _
  have hqq : ∀ w : X I, qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w := by
    intro w
    simp only [qq, hφ]
    exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' *
          f fun i => w' (σ i)) (φ w) := by
        congr 1; funext w; simp only [hqq, hφ, Equiv.symm_apply_apply]
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : X (Fin (Fintype.card I)) =>
          qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f fun i => z (σ.symm (σ i)) := fin_case ha hb h3 hK _ _ (fun v => hk _) _ hsep C hbd _
    _ = f z := by simp only [Equiv.symm_apply_apply]

end UpperTheory.Esk.MultivariableReproducingLemmas

open UpperTheory.Esk.MultivariableReproducingLemmas in
theorem UpperTheory.Esk.multivariable_reproducing_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B3 → UpperTheory.Esk.KapInt → UpperTheory.Esk.MultivariableReproducingFormula := by
  intro ha hb h3 hK I _ k hk f hf hC z
  obtain ⟨C, hC⟩ := hC
  exact ⟨integrable hb hK k hk f hf.1 C hC z, main ha hb h3 hK I k hk f hf C hC z⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.OrbitCoverProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.OrbitCoverLemmas

variable {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]

omit [Countable G] [MeasurableSpace Y] in

theorem orbit_tsum_smul (u : Y → ℝ) (g : G) (y : Y) :
    ∑' h : G, u (h • g • y) = ∑' h : G, u (h • y) := by
  simp only [smul_smul]
  exact (Equiv.mulRight g).tsum_eq (fun h => u (h • y))

theorem exists_cut (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y))
    (hs : ∀ y, Summable fun g : G => u (g • y)) : ∃ b : Y → ℝ, IsCut G b := by
  have hsE : (fun y => ∑' g : G, u (g • y)) =
      fun y => (∑' g : G, ENNReal.ofReal (u (g • y))).toReal := by
    funext y
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => h0 _) (hs y), ENNReal.toReal_ofReal]
    exact tsum_nonneg fun g => h0 _
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [hsE]
    exact (Measurable.ennreal_tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos : ∀ y, 0 < ∑' g : G, u (g • y) := by
    intro y
    obtain ⟨g, hg⟩ := hpos y
    exact lt_of_lt_of_le hg ((hs y).le_tsum g fun h _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y),
    ⟨hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩⟩
  have : (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) =
      fun g => u (g • y) / ∑' h : G, u (h • y) := by
    funext g; rw [orbit_tsum_smul]
  show HasSum (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) 1
  rw [this, ← div_self (hspos y).ne']
  exact (hs y).hasSum.div_const _

theorem cover (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) :
    ∫⁻ y, ENNReal.ofReal (b y) ∂μ ≤ μ S :=
  _root_.UpperTheory.Reformulated.B.Qf46.cover μ hP b hb S hS hc

end UpperTheory.Esk.OrbitCoverLemmas

theorem UpperTheory.Esk.orbit_cover_proof : UpperTheory.Esk.C2 := by
  intro G Y _ _ _ _
  exact ⟨fun hm u hu h0 hpos hs => UpperTheory.Esk.OrbitCoverLemmas.exists_cut hm u hu h0 hpos hs,
    fun μ hP b hb S hS hc => UpperTheory.Esk.OrbitCoverLemmas.cover μ hP b hb S hS hc⟩
end
end


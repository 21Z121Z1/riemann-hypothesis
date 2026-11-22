import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0003
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0009

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLocGap
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

open Formalism.MainNotions.CayleySignature

theorem lt_sub_of_increments {m : ℕ} (b : Fin m → ℝ) (G : ℝ) (hG : 0 < G)
    (h : ∀ (j : Fin m) (hj : j.val + 1 < m), G < b ⟨j.val + 1, hj⟩ - b j) :
    ∀ i j : Fin m, i < j → G < b j - b i := by
  intro i j hij
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij' : i < j := hij
  clear hij
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 : G < b ⟨j + 1, hj⟩ - b ⟨j, by omega⟩ := h ⟨j, by omega⟩ hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij' with hlt | heq
    · have h2 := ih (by omega) hlt
      linarith
    · subst heq
      exact h1

theorem lt_abs_sub_of_increments {m : ℕ} (b : Fin m → ℝ) (G : ℝ) (hG : 0 < G)
    (h : ∀ (j : Fin m) (hj : j.val + 1 < m), G < b ⟨j.val + 1, hj⟩ - b j)
    (i j : Fin m) (hij : i ≠ j) : G < |b i - b j| := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have := lt_sub_of_increments b G hG h i j hlt
    exact lt_abs.mpr (Or.inr (by linarith))
  · have := lt_sub_of_increments b G hG h j i hlt
    exact lt_abs.mpr (Or.inl (by linarith))

theorem cayley_weight_high_index (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : Fin (2 * r + k + 1)) (hi : ¬ i.val < k - 1) :
    lam48 k r v b i = -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩ := by
  unfold lam48
  exact dif_neg hi

theorem gapAtLeast_of_increments (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (G : ℝ) (hG : 0 < G)
    (hanti : StrictAnti (lam48 k r v b))
    (hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), G < b ⟨j.val + 1, hj⟩ - b j) :
    GapAtLeast (eps48 k r) (lam48 k r v b) G := by
  have key : ∀ a c : Fin (2 * r + k + 1), a.val < k - 1 → ¬ c.val < k - 1 → (c.val - (k - 1)) % 2 = 1 →
      G ≤ |lam48 k r v b a - lam48 k r v b c| := by
    intro a c ha hc hpar
    have hk : k - 1 < 2 * r + k + 1 := by omega
    have h1 := hanti (show a < ⟨k - 1, hk⟩ by rw [Fin.lt_def]; exact ha)
    rw [cayley_weight_high_index k r v b ⟨k - 1, hk⟩ (by simp)] at h1
    simp only [Nat.sub_self] at h1
    rw [cayley_weight_high_index k r v b c hc]
    have h2 := lt_sub_of_increments b G hG hb ⟨0, by omega⟩ ⟨c.val - (k - 1), by have := c.isLt; omega⟩
      (by rw [Fin.lt_def]; simp only; omega)
    refine le_trans ?_ (le_abs_self _)
    linarith
  intro a c hac
  by_cases ha : a.val < k - 1 <;> by_cases hc : c.val < k - 1
  · exfalso; apply hac; simp only [eps48, if_pos ha, if_pos hc]
  · have hp : (c.val - (k - 1)) % 2 = 1 := by
      by_contra hne
      apply hac
      simp only [eps48, if_pos ha, if_neg hc]
      simp [show (c.val - (k - 1)) % 2 = 0 by omega]
    exact key a c ha hc hp
  · have hp : (a.val - (k - 1)) % 2 = 1 := by
      by_contra hne
      apply hac
      simp only [eps48, if_pos hc, if_neg ha]
      simp [show (a.val - (k - 1)) % 2 = 0 by omega]
    rw [abs_sub_comm]; exact key c a hc ha hp
  · rw [cayley_weight_high_index k r v b a ha, cayley_weight_high_index k r v b c hc]
    have hne : (⟨c.val - (k - 1), by have := c.isLt; omega⟩ : Fin (2 * r + 2)) ≠
        ⟨a.val - (k - 1), by have := a.isLt; omega⟩ := by
      intro heq
      apply hac
      have hv : c.val - (k - 1) = a.val - (k - 1) := congrArg Fin.val heq
      simp only [eps48, if_neg ha, if_neg hc]
      rw [hv]
    have := lt_abs_sub_of_increments b G hG hb _ _ hne
    rw [show -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ - -b ⟨c.val - (k - 1), by have := c.isLt; omega⟩ =
      b ⟨c.val - (k - 1), by have := c.isLt; omega⟩ - b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ by ring]
    exact this.le

theorem q_le_of_cayley_signature (k r : ℕ) : qOf (eps48 k r) ≤ r + 1 := by
  have hodd : ∀ x : Fin (2 * r + k + 1), eps48 k r x = false →
      ¬ x.val < k - 1 ∧ (x.val - (k - 1)) % 2 = 1 := by
    intro x hx
    unfold eps48 at hx
    by_cases h1 : x.val < k - 1
    · rw [if_pos h1] at hx
      exact absurd hx (by decide)
    · rw [if_neg h1] at hx
      refine ⟨h1, ?_⟩
      have h2 : ¬ ((x.val - (k - 1)) % 2 = 0) := by simpa using hx
      omega
  unfold qOf
  calc (Finset.univ.filter fun a => eps48 k r a = false).card
      ≤ (Finset.range (r + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin (2 * r + k + 1) => (a.val - (k - 1)) / 2)
        · intro a _
          simp only [Finset.mem_coe, Finset.mem_range]
          have := a.isLt
          omega
        · intro a ha c hc hac
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
          have h1 := hodd a ha
          have h2 := hodd c hc
          dsimp only at hac
          apply Fin.ext
          omega
    _ = r + 1 := Finset.card_range _

theorem cubic_bound_of_gap_nat (n r t M : ℕ) (hM : M = n + (2 * r + 2) * t) (ht : n + 5 ≤ t) :
    96 * n ^ 2 * (r + 1) ≤ 2 * M ^ 3 := by
  subst hM
  have ht2 : 2 * t ≤ (2 * r + 2) * t := Nat.mul_le_mul (by omega) le_rfl
  have hr : 10 * (r + 1) ≤ (2 * r + 2) * t := by
    calc 10 * (r + 1) ≤ (2 * r + 2) * 5 := by omega
      _ ≤ (2 * r + 2) * t := Nat.mul_le_mul le_rfl (by omega)
  set X := (2 * r + 2) * t with hX
  have h3 : 3 * n ≤ n + X := by omega
  have h10 : 10 * (r + 1) ≤ n + X := by omega
  calc 96 * n ^ 2 * (r + 1) ≤ 2 * ((3 * n) * (3 * n) * (10 * (r + 1))) := by
        nlinarith [Nat.zero_le (n ^ 2 * r), Nat.zero_le (n ^ 2)]
    _ ≤ 2 * ((n + X) * (n + X) * (n + X)) := by gcongr
    _ = 2 * (n + X) ^ 3 := by ring

theorem cayley_weight_gap (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hlam : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hgap : Formalism.MainNotions.CayleySignature.GapBig k r b) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h ∧
      (1 ≤ S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r) →
        ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ) * (qOf (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ) + 1 < h ∧
        8 * Real.sqrt (2 * (S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ)) *
            (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) +
              2 * ((2 * r + k + 1 : ℕ) : ℝ) * S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r)) < h) := by
  obtain ⟨t, -, ht1, -, ht⟩ := hgap
  have ht1' : 2 * r + k + 1 + 5 ≤ t := ht1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * r + k + 1 + (2 * r + 2) * t := ⟨_, rfl⟩
  have hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * (M : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j := by
    rw [hM]; exact ht
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have htpos : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  refine ⟨2 * (M : ℝ) ^ 3 + (t : ℝ) + 3, ?_, ?_⟩
  · exact gapAtLeast_of_increments k r v b _ (by positivity) hlam.1 hb
  · intro _
    have hq : qOf (eps48 k r) ≤ r + 1 := q_le_of_cayley_signature k r
    have hpn : pOf (eps48 k r) ≤ 2 * r + k + 1 := by
      unfold pOf; exact (Finset.card_filter_le _ _).trans (by simp)
    have hqn : qOf (eps48 k r) ≤ 2 * r + k + 1 := by
      unfold qOf; exact (Finset.card_filter_le _ _).trans (by simp)
    have hq0 : S7.q0 (eps48 k r) ≤ r + 1 := (min_le_right _ _).trans hq
    have hnM : 2 * r + k + 1 ≤ M := by rw [hM]; omega
    have hnat1 : (2 * r + k + 1) * pOf (eps48 k r) * qOf (eps48 k r) ≤ M ^ 3 := by
      calc _ ≤ M * M * M := Nat.mul_le_mul (Nat.mul_le_mul hnM (hpn.trans hnM)) (hqn.trans hnM)
        _ = M ^ 3 := by ring
    have hnat2 := cubic_bound_of_gap_nat (2 * r + k + 1) r t M hM ht1'
    have c1 : ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (eps48 k r) : ℝ) * (qOf (eps48 k r) : ℝ) ≤ (M : ℝ) ^ 3 := by
      exact_mod_cast hnat1
    have c2 : (96 : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) ^ 3 := by
      exact_mod_cast hnat2
    have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
    refine ⟨by linarith, ?_⟩
    have hN0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ (S7.q0 (eps48 k r) : ℝ) := Nat.cast_nonneg _
    have hR1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
    have hRN : ((r + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ 2 * r + k + 1)
    have hQR : (S7.q0 (eps48 k r) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast hq0
    have hs0 := Real.sqrt_nonneg (2 * (S7.q0 (eps48 k r) : ℝ))
    have hu0 := Real.sqrt_nonneg (2 * ((r + 1 : ℕ) : ℝ))
    have hu2 : Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 = 2 * ((r + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    have hsu : Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hu1' : 1 ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) := by nlinarith
    have hu1 : Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ≤ 2 * ((r + 1 : ℕ) : ℝ) := by nlinarith
    have hsu' : Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ≤
        2 * ((r + 1 : ℕ) : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hsu hu0]
    have hQs : (S7.q0 (eps48 k r) : ℝ) * Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) ≤
        ((r + 1 : ℕ) : ℝ) * (2 * ((r + 1 : ℕ) : ℝ)) :=
      mul_le_mul hQR (hsu.trans hu1) hs0 (by linarith)
    have p1 := mul_le_mul_of_nonneg_left hsu' (sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ))
    have p2 := mul_le_mul_of_nonneg_left hQs hN0
    have p3 := mul_le_mul_of_nonneg_left hRN (mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)))
    nlinarith [p1, p2, p3, c2]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdl_inner_continuous {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    Continuous (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) := by
  have hpm : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
    first
    | exact (JacB.pmatLin ε).continuous_of_finiteDimensional
    | exact (dpbE ε).continuous_of_finiteDimensional
    | (refine continuous_pi fun a => continuous_pi fun b => ?_
       unfold pmat
       split_ifs <;> fun_prop)
  have hmk : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    | (unfold toMK toM; fun_prop)
  have hM : Continuous fun p : (PCoord ε → ℂ) × KG ε => toMK p.2⁻¹ * pmat p.1 * toMK p.2 :=
    ((hmk.comp continuous_snd.inv).matrix_mul (hpm.comp continuous_fst)).matrix_mul
      (hmk.comp continuous_snd)
  have hPh : Continuous fun p : (PCoord ε → ℂ) × KG ε => Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2) :=
    continuous_potential_comp lam hM (fun p => ⟨adK p.2⁻¹ p.1, conj_pmat_eq_adK p.2 p.1⟩)
  have hop : Continuous fun p : (PCoord ε → ℂ) × KG ε => T.op p.2 :=
    (continuous_subtype_val.comp T.cont).comp continuous_snd
  have hF : Continuous fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) *
        (⟪T.op p.2 T.w, v⟫_ℂ * ⟪u, T.op p.2 T.w⟫_ℂ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hPh.neg)).mul
      (((hop.clm_apply continuous_const).inner continuous_const).mul
        (continuous_const.inner (hop.clm_apply continuous_const)))
  have hI := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun (z : PCoord ε → ℂ) (k : KG ε) =>
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)) hF isCompact_univ
  simp only [Measure.restrict_univ] at hI
  have he : (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) = fun z =>
      ((Module.finrank ℂ T.V : ℝ) : ℂ) *
        ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
          (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε) := by
    funext z
    exact inner_fF_eq_integral lam T z u v
  rw [he]
  exact continuous_const.mul hI

theorem fdl_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i)))),
    integral_fintype_prod_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))

theorem fdl_cgauss {c : ℝ} (hc : 0 < c) : ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = Real.pi / c := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hc
  simp only [neg_mul, Complex.finrank_real_complex] at h
  rw [h]
  norm_num

theorem fdl_cgauss_int {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  apply Integrable.of_integral_ne_zero
  rw [fdl_cgauss hc]
  exact (div_pos Real.pi_pos hc).ne'

theorem fdl_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  have h : (b : ℕ) < (a : ℕ) := hab.1
  have h' : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast h
  show 0 < (0 : Fin n → ℝ) b - (0 : Fin n → ℝ) a + ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)
  simp only [Pi.zero_apply, sub_zero, zero_add]
  linarith

theorem fdl_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hw : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := fdl_wab_zero_pos
  have h1 : ∀ y : PCoord ε → ℂ, Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab, Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2)) := by
    intro y
    rw [Qf, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [h1]
  rw [MeasureTheory.volume_pi]
  rw [fdl_lint_pi_ofReal (E := fun _ : PCoord ε => ℂ) (μ := fun _ => volume)
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖x‖ ^ 2)))
    (fun ab => fdl_cgauss_int (hw ab)) (fun _ _ => (Real.exp_pos _).le)]
  rw [PiW, ENNReal.ofReal_prod_of_nonneg (fun ab _ => (div_pos Real.pi_pos (hw ab)).le)]
  exact Finset.prod_congr rfl fun ab _ => by rw [fdl_cgauss (hw ab)]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacAll
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jall_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem jall_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

def adKL {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, jall_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, jall_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, Pi.smul_apply, Matrix.smul_apply,
      RingHom.id_apply, Complex.real_smul, smul_eq_mul]

theorem jall_adK_inv {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : adK k⁻¹ (adK k z) = z := by
  have hk := toMK_facts k
  have h : pmat (adK k⁻¹ (adK k z)) = pmat z := by
    rw [pmat_adK, pmat_adK, toMK_inv, Matrix.conjTranspose_conjTranspose]
    calc (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ) * toMK k
        = ((toMK k)ᴴ * toMK k) * pmat z * ((toMK k)ᴴ * toMK k) := by simp only [Matrix.mul_assoc]
      _ = pmat z := by rw [hk.1, Matrix.one_mul, Matrix.mul_one]
  rw [← pact_pmat_coords (adK k⁻¹ (adK k z)), h, pact_pmat_coords]

theorem jall_abs_det_adKL {ε : Fin n → Bool} (k : KG ε) : |LinearMap.det (adKL k)| = 1 := by
  have hinj : Function.Injective (adKL k) := fun x y hxy => by
    have := congrArg (adK k⁻¹) hxy
    simpa only [adKL, LinearMap.coe_mk, AddHom.coe_mk, jall_adK_inv] using this
  have hmp := adK_measurePreserving k
  have hcs : IsCompact ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    (isCompact_closedBall 0 1).image (LinearMap.continuous_of_finiteDimensional _)
  have h1 : volume ((adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1)) =
      volume ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    hmp.measure_preimage hcs.isClosed.measurableSet.nullMeasurableSet
  have hpre : (adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) =
      Metric.closedBall (0 : PCoord ε → ℂ) 1 := Set.preimage_image_eq _ hinj
  rw [hpre, MeasureTheory.Measure.addHaar_image_linearMap] at h1
  have hpos : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hfin : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : PCoord ε → ℂ) 1).measure_lt_top.ne
  have h2 : ENNReal.ofReal |LinearMap.det (adKL k)| = 1 := by
    have h3 : 1 * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) =
        ENNReal.ofReal |LinearMap.det (adKL k)| * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).mp h3).symm
  exact ENNReal.ofReal_eq_one.mp h2

def jdetA {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : ℝ :=
  LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
    (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))

theorem jall_diff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    DifferentiableAt ℝ (actR (ε := ε) g) z := by
  first
  | exact (JacB.actR_contDiff' hg).differentiable one_ne_zero z
  | exact (JacB.actR_contDiff' hg).differentiable le_rfl z

theorem jall_chain {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : jdetA (g * h) z = jdetA h (actR g z) * jdetA g z := by
  unfold jdetA
  have hfun : actR (ε := ε) (g * h) = actR h ∘ actR g := funext (actR_mul hg hh)
  rw [hfun, fderiv_comp z (jall_diff hh (actR g z)) (jall_diff hg z)]
  exact LinearMap.det_comp _ _

theorem jall_fderiv_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    fderiv ℝ (actR (ε := ε) (toMK k)) z = LinearMap.toContinuousLinearMap (adKL k⁻¹) := by
  have e : actR (ε := ε) (toMK k) = ⇑(LinearMap.toContinuousLinearMap (adKL k⁻¹)) := by
    funext w
    rw [actR_K]
    rfl
  rw [e]
  exact ContinuousLinearMap.fderiv _

theorem jall_abs_jdetA_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    |jdetA (toMK k) z| = 1 := by
  unfold jdetA
  rw [jall_fderiv_K]
  exact jall_abs_det_adKL k⁻¹

theorem jall_inUJ_K {ε : Fin n → Bool} (k : KG ε) : inUJ ε (toMK k) := by
  first
  | exact k.1.2
  | exact k.val.property
  | exact k.2.1

theorem jall_actR_K_zero {ε : Fin n → Bool} (k : KG ε) : actR (ε := ε) (toMK k) 0 = 0 := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  apply actR_of_eq_polarM (k := k)
  simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]

theorem jacAll {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac (actR g z) = Jac z := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  obtain ⟨k, hk⟩ := actR_spec hg z
  set w := actR g z with hw
  have hEz := exp_pmat_inUJ z
  have hEw := exp_pmat_inUJ w
  have hK := jall_inUJ_K k
  have h0z : actR (ε := ε) (NormedSpace.exp (pmat z)) 0 = z := by
    apply actR_of_eq_polarM (k := 1)
    simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul]
    first
    | rfl
    | (rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.one_mul])
    | simp
  have hc1 := jall_chain hEz hg 0
  rw [h0z] at hc1
  have hc2 := jall_chain hK hEw 0
  rw [jall_actR_K_zero] at hc2
  have hmul : NormedSpace.exp (pmat z) * g = toMK k * NormedSpace.exp (pmat w) := by
    rw [hk]; rfl
  rw [hmul, hc2] at hc1
  have hab : |jdetA g z| * |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| = |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| := by
    have := congrArg abs hc1
    rw [abs_mul, abs_mul, jall_abs_jdetA_K, mul_one] at this
    rw [this, mul_comm]
  have hbZ : |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| * Jac z = 1 := JacB.jacBase' z
  have hcW : |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| * Jac w = 1 := JacB.jacBase' w
  show |jdetA g z| * Jac w = Jac z
  linear_combination (-(|jdetA g z| * Jac w)) * hbZ + (Jac w * Jac z) * hab + Jac z * hcW

end ReciprocityTheory.ChartRestriction.DS
end
end


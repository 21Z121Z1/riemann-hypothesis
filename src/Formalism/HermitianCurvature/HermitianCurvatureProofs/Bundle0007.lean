import Formalism.HermitianCurvature.Bundle0001
import Mathlib
import Formalism.HermitianCurvature.StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SharpRecursion
section
namespace Formalism.FourierDecayAlt.P.Rec

open Finset Real

lemma geom_le (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1/2) :
    ∀ i : ℕ, ∑ t ∈ Icc 2 i, a ^ (t-1) ≤ 2 * a := by
  have aux : ∀ k : ℕ, ∑ t ∈ Icc 2 (k+1), a ^ (t-1) + 2 * a ^ (k+1) ≤ 2 * a := by
    intro k
    induction k with
    | zero =>
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : k + 1 + 1 - 1 = k + 1 := by omega
      rw [e]
      have hp := pow_nonneg h0 (k+1)
      have hs : a ^ (k + 1 + 1) = a ^ (k+1) * a := pow_succ a (k+1)
      rw [hs]
      nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  intro i
  rcases i with _ | k
  · rw [Finset.Icc_eq_empty (by norm_num)]; simp; linarith
  · have := aux k
    have hp := pow_nonneg h0 (k+1)
    linarith

noncomputable def Pp (e : ℕ → ℝ) (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, √(1 + e l)

lemma Pp_zero (e : ℕ → ℝ) : Pp e 0 = 1 := by
  simp [Pp]

lemma Pp_succ (e : ℕ → ℝ) (i : ℕ) : Pp e (i+1) = Pp e i * √(1 + e (i+1)) := by
  unfold Pp
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma one_le_sqrt_e {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (l : ℕ) : (1:ℝ) ≤ √(1 + e l) := by
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + e l by linarith [he l])
  rwa [Real.sqrt_one] at this

lemma one_le_Pp {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : ∀ i, 1 ≤ Pp e i := by
  intro i
  induction i with
  | zero => rw [Pp_zero]
  | succ k ih =>
    rw [Pp_succ]
    have := one_le_sqrt_e he (k+1)
    nlinarith

lemma Pp_nonneg {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) : 0 ≤ Pp e i :=
  le_trans zero_le_one (one_le_Pp he i)

lemma Pp_mono {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : Monotone (Pp e) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Pp_succ]
  exact le_mul_of_one_le_right (Pp_nonneg he n) (one_le_sqrt_e he (n+1))

lemma Pp_sq {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) :
    Pp e i ^ 2 = ∏ l ∈ Icc 1 i, (1 + e l) := by
  unfold Pp
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro l _
  rw [Real.sq_sqrt (by linarith [he l])]

lemma growth (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ) (ρ : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hε : 0 ≤ ε) (he : ∀ i, 0 ≤ e i) (hσ : ∀ i, 0 ≤ σ i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t))
    (hρ1 : 1 + ε + 2 * a ≤ ρ) :
    ∀ i, i ≤ r + 1 → σ i ≤ Pp e i * ρ ^ i * σ 0 := by
  have hρ : (1:ℝ) ≤ ρ := by linarith
  have hσ0 := hσ 0
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · simp [Pp_zero]
    · have h1 := hrec (k+1) (by omega) hi
      simp only [Nat.add_sub_cancel] at h1
      have hB : 0 ≤ Pp e (k+1) * ρ ^ k * σ 0 :=
        mul_nonneg (mul_nonneg (Pp_nonneg he _) (pow_nonneg (by linarith) _)) hσ0
      have hsum : ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t) ≤
          2 * a * (Pp e (k+1) * ρ ^ k * σ 0) := by
        calc ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t)
            ≤ ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * (Pp e (k+1) * ρ ^ k * σ 0) := by
              apply Finset.sum_le_sum
              intro t ht
              have ht' := Finset.mem_Icc.mp ht
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha _)
              calc σ (k+1-t) ≤ Pp e (k+1-t) * ρ ^ (k+1-t) * σ 0 := ih _ (by omega) (by omega)
                _ ≤ Pp e (k+1) * ρ ^ k * σ 0 := by
                  apply mul_le_mul_of_nonneg_right _ hσ0
                  exact mul_le_mul (Pp_mono he (by omega)) (pow_le_pow_right₀ hρ (by omega))
                    (pow_nonneg (by linarith) _) (Pp_nonneg he _)
          _ = (∑ t ∈ Icc 2 (k+1), a ^ (t-1)) * (Pp e (k+1) * ρ ^ k * σ 0) := by
              rw [Finset.sum_mul]
          _ ≤ 2 * a * (Pp e (k+1) * ρ ^ k * σ 0) :=
              mul_le_mul_of_nonneg_right (geom_le a ha ha2 _) hB
      have h3 := ih k (by omega) (by omega)
      have hs1 : 0 ≤ √(1 + e (k+1)) := Real.sqrt_nonneg _
      have hc : 0 ≤ (1 + ε) * √(1 + e (k+1)) := mul_nonneg (by linarith) hs1
      calc σ (k+1) ≤ (1 + ε) * √(1 + e (k+1)) * σ k +
            ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t) := h1
        _ ≤ (1 + ε) * √(1 + e (k+1)) * (Pp e k * ρ ^ k * σ 0) +
            2 * a * (Pp e (k+1) * ρ ^ k * σ 0) :=
            add_le_add (mul_le_mul_of_nonneg_left h3 hc) hsum
        _ = (1 + ε + 2 * a) * (Pp e (k+1) * ρ ^ k * σ 0) := by rw [Pp_succ]; ring
        _ ≤ ρ * (Pp e (k+1) * ρ ^ k * σ 0) := mul_le_mul_of_nonneg_right hρ1 hB
        _ = Pp e (k+1) * ρ ^ (k+1) * σ 0 := by rw [pow_succ]; ring

lemma quart (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : (1 + 2 * x) ^ 4 ≤ 1 + 80 * x := by
  have h2 : x ^ 2 ≤ x := by nlinarith
  have h3 : x ^ 3 ≤ x := by nlinarith
  have h4 : x ^ 4 ≤ x := by nlinarith
  nlinarith

lemma pow_bound (r : ℕ) (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hx : ((r:ℝ) + 1) * (ε + a) ≤ 1) :
    ((1 + ε + 2 * a) ^ (r+1)) ^ 2 ≤ 1 + 80 * ((r:ℝ) + 1) * (ε + a) := by
  have hx0 : 0 ≤ ((r:ℝ) + 1) * (ε + a) := by positivity
  have h1 : 1 + ε + 2 * a ≤ Real.exp (2 * (ε + a)) := by
    have := Real.add_one_le_exp (2 * (ε + a)); linarith
  have h2 : (1 + ε + 2 * a) ^ (r+1) ≤ Real.exp (((r+1 : ℕ) : ℝ) * (2 * (ε + a))) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by linarith) h1 _
  have h3 : Real.exp (((r+1 : ℕ) : ℝ) * (2 * (ε + a))) =
      Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h3] at h2
  have hE := Real.abs_exp_sub_one_le (x := ((r:ℝ) + 1) * (ε + a))
    (by rw [abs_of_nonneg hx0]; exact hx)
  rw [abs_of_nonneg hx0] at hE
  have hE' : Real.exp (((r:ℝ) + 1) * (ε + a)) ≤ 1 + 2 * (((r:ℝ) + 1) * (ε + a)) := by
    linarith [le_abs_self (Real.exp (((r:ℝ) + 1) * (ε + a)) - 1)]
  have hEn : 0 ≤ Real.exp (((r:ℝ) + 1) * (ε + a)) := (Real.exp_pos _).le
  have hρn : 0 ≤ (1 + ε + 2 * a) ^ (r+1) := pow_nonneg (by linarith) _
  have s1 := pow_le_pow_left₀ hρn h2 2
  have s2 := pow_le_pow_left₀ hEn hE' 4
  have s3 := quart (((r:ℝ) + 1) * (ε + a)) hx0 hx
  have e4 : (Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 2) ^ 2 =
      Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 4 := by ring
  have e5 : 80 * ((r:ℝ) + 1) * (ε + a) = 80 * (((r:ℝ) + 1) * (ε + a)) := by ring
  rw [e5]
  linarith

end Formalism.FourierDecayAlt.P.Rec

namespace Formalism.FourierDecayAlt.P

open Finset Real Formalism.FourierDecayAlt.P.Rec

theorem sharp_recursion : Formalism.FourierDecayAlt.RecursionSharp := by
  refine ⟨80, ?_⟩
  intro r a ε e σ ha ha2 hε hx he hσ hrec
  have hg := growth r a ε e σ (1 + ε + 2 * a) ha ha2 hε he hσ hrec le_rfl (r+1) le_rfl
  have hpb := pow_bound r a ε ha hε hx
  have hsq := pow_le_pow_left₀ (hσ (r+1)) hg 2
  have hPs := Pp_sq he (r+1)
  have hσ0 : 0 ≤ σ 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hPs]; exact sq_nonneg _
  calc σ (r+1) ^ 2 ≤ (Pp e (r+1) * (1 + ε + 2 * a) ^ (r+1) * σ 0) ^ 2 := hsq
    _ = ((1 + ε + 2 * a) ^ (r+1)) ^ 2 * (Pp e (r+1) ^ 2) * σ 0 ^ 2 := by ring
    _ = ((1 + ε + 2 * a) ^ (r+1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
        rw [hPs]
    _ ≤ (1 + 80 * ((r : ℝ) + 1) * (ε + a)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hσ0
        exact mul_le_mul_of_nonneg_right hpb hprod

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralPsiMoving
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_psi (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  unfold G.psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_psi (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop

def freq (β w : ℂ) : ℂ := ((2 * Real.pi)⁻¹ : ℝ) • (-(conj (β * w)))

theorem psi_eq_fourierChar (β w z : ℂ) :
    G.psi β (w * z) = ((Real.fourierChar (-⟪z, freq β w⟫_ℝ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, G.psi, freq, real_inner_smul_right, Complex.inner]
  congr 1
  have hre : (-conj (β * w) * conj z).re = -(β * (w * z)).re := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  rw [hre]
  push_cast
  field_simp

theorem tendsto_freq (β : ℂ) (hβ : β ≠ 0) : Tendsto (freq β) (cocompact ℂ) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded, Metric.cobounded_eq_cocompact]
  have hn : ∀ w, ‖freq β w‖ = ((2 * Real.pi)⁻¹ * ‖β‖) * ‖w‖ := by
    intro w
    rw [freq, norm_smul, norm_neg, Complex.norm_conj, norm_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  simp_rw [hn]
  exact (tendsto_norm_cocompact_atTop).const_mul_atTop (by positivity)

theorem tendsto_integral_psi (β : ℂ) (hβ : β ≠ 0) (f : ℂ → E) :
    Tendsto (fun w => ∫ z, G.psi β (w * z) • f z) (cocompact ℂ) (𝓝 0) := by
  have RL := (tendsto_integral_exp_inner_smul_cocompact f).comp (tendsto_freq β hβ)
  refine RL.congr fun w => ?_
  simp only [Function.comp_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [psi_eq_fourierChar, Circle.smul_def]

theorem norm_integral_psi_sub_le (β w : ℂ) (f g : ℂ → E) (hf : Integrable f) (hg : Integrable g) :
    ‖(∫ z, G.psi β (w * z) • f z) - ∫ z, G.psi β (w * z) • g z‖ ≤ ∫ z, ‖f z - g z‖ := by
  have hfi : Integrable (fun z => G.psi β (w * z) • f z) :=
    hf.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  have hgi : Integrable (fun z => G.psi β (w * z) • g z) :=
    hg.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) (hf.sub hg).norm (Eventually.of_forall fun z => ?_))
  simp only [← smul_sub, norm_smul, norm_psi, one_mul, le_refl]

theorem tendsto_integral_psi_moving {α : Type} {l : Filter α} (β : ℂ) (hβ : β ≠ 0) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (hw : Tendsto w l (cocompact ℂ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 0) := by
  have h0 := (tendsto_integral_psi β hβ f0).comp hw
  rw [← add_zero (0 : E)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0

theorem continuous_integral_psi (β : ℂ) (f : ℂ → E) (hf : Integrable f) :
    Continuous (fun w => ∫ z, G.psi β (w * z) • f z) := by
  refine continuous_of_dominated (bound := fun z => ‖f z‖) (fun w => ?_) (fun w => ?_) hf.norm ?_
  · exact (((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable).smul hf.1
  · exact Eventually.of_forall fun z => by rw [norm_smul, norm_psi, one_mul]
  · exact Eventually.of_forall fun z =>
      ((continuous_psi β).comp (continuous_id.mul continuous_const)).smul continuous_const

theorem tendsto_integral_psi_conv {α : Type} {l : Filter α} (β : ℂ) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (σ : ℂ) (hw : Tendsto w l (𝓝 σ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 (∫ z, G.psi β (σ * z) • f0 z)) := by
  have h0 := ((continuous_integral_psi β f0 hf0).tendsto σ).comp hw
  rw [← zero_add (∫ z, G.psi β (σ * z) • f0 z)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
section
namespace Formalism.FourierDecayAlt.P.Misc

open Formalism.FourierDecayAlt.I Finset Polynomial

theorem selfDualG_holds : SelfDualG := by
  intro F _ o q hq hq0 a
  constructor
  · intro h
    have h1 := h (1, 1) ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by simp⟩
    have h2 := h (q, 0) ⟨hq, o.zero_mem, 1, o.one_mem, by simp⟩
    simp only [mul_one, mul_zero, sub_zero] at h1 h2
    have e2 : a.1 * q / q = a.1 := by field_simp
    rw [e2] at h2
    refine ⟨h2, ?_, (a.1 - a.2) / q, h1, by field_simp⟩
    have : a.2 = a.1 - q * ((a.1 - a.2) / q) := by field_simp; ring
    rw [this]; exact o.sub_mem h2 (o.mul_mem hq h1)
  · rintro ⟨ha1, ha2, s, hs, has⟩ b ⟨hb1, hb2, t, ht, hbt⟩
    have ha : a.1 = a.2 + q * s := by linear_combination has
    have hb : b.1 = b.2 + q * t := by linear_combination hbt
    have e : (a.1 * b.1 - a.2 * b.2) / q = a.2 * t + s * b.2 + q * s * t := by
      rw [ha, hb]; field_simp; ring
    rw [e]
    exact o.add_mem (o.add_mem (o.mul_mem ha2 ht) (o.mul_mem hs hb2)) (o.mul_mem (o.mul_mem hq hs) ht)

lemma tpolyProd_succ {A : Type} [Ring A] (n : ℕ) (p c ci : ℕ → A) :
    TpolyProd (n + 1) p c ci = Tpoly (p (n + 1)) (c (n + 1)) (ci (n + 1)) * TpolyProd n p c ci := by
  rw [TpolyProd, TpolyProd, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  simp [List.prod_cons]

theorem tProdMonic_holds : TProdMonic := by
  intro A _ _ n p c ci
  induction n with
  | zero => simp [TpolyProd]
  | succ n ih =>
    obtain ⟨hm, hd, hb⟩ := ih
    have e00 : TpolyProd (n + 1) p c ci 0 0 =
        (X + C (p (n + 1))) * TpolyProd n p c ci 0 0 - C (c (n + 1)) * TpolyProd n p c ci 1 0 := by
      rw [tpolyProd_succ]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
    have e10 : TpolyProd (n + 1) p c ci 1 0 = C (ci (n + 1)) * TpolyProd n p c ci 0 0 := by
      rw [tpolyProd_succ]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two]
    have hXm : (X + C (p (n + 1)) : A[X]).Monic := monic_X_add_C _
    have hprod : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).Monic := hXm.mul hm
    have hpd : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).natDegree = n + 1 := by
      rw [hXm.natDegree_mul hm, natDegree_X_add_C, hd]; ring
    have hlow : (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree <
        ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).degree := by
      rw [degree_eq_natDegree hprod.ne_zero, hpd]
      calc (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree
          ≤ (C (c (n + 1))).degree + (TpolyProd n p c ci 1 0).degree := degree_mul_le _ _
        _ ≤ 0 + (TpolyProd n p c ci 1 0).degree := by gcongr; exact degree_C_le
        _ < (n : WithBot ℕ) := by simpa using hb
        _ ≤ ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.le_succ n
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; exact hprod.sub_of_left hlow
    · rw [e00]; exact (natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlow)).trans hpd
    · rw [e10]
      calc (C (ci (n + 1)) * TpolyProd n p c ci 0 0).degree
          ≤ (C (ci (n + 1))).degree + (TpolyProd n p c ci 0 0).degree := degree_mul_le _ _
        _ ≤ 0 + (TpolyProd n p c ci 0 0).degree := by gcongr; exact degree_C_le
        _ = (n : WithBot ℕ) := by rw [zero_add, degree_eq_natDegree hm.ne_zero, hd]
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self n

end Formalism.FourierDecayAlt.P.Misc

theorem Formalism.FourierDecayAlt.P.self_dual_gamma : Formalism.FourierDecayAlt.I.SelfDualG := Formalism.FourierDecayAlt.P.Misc.selfDualG_holds
theorem Formalism.FourierDecayAlt.P.transfer_product_monic : Formalism.FourierDecayAlt.I.TProdMonic := Formalism.FourierDecayAlt.P.Misc.tProdMonic_holds
end


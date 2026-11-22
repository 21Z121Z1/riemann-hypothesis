import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentation
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RepBound

theorem poly_bound {σ : Type} (P : MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ‖aeval x P‖ ≤ C * B ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖(a : ℂ)‖, 0, norm_nonneg _, fun B _ x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    obtain ⟨C2, d2, h2, hq⟩ := hq
    refine ⟨C1 + C2, d1 + d2, by positivity, fun B hB x hx => ?_⟩
    rw [map_add]
    have e1 : B ^ d1 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    have e2 : B ^ d2 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    calc ‖aeval x p + aeval x q‖ ≤ ‖aeval x p‖ + ‖aeval x q‖ := norm_add_le _ _
      _ ≤ C1 * B ^ d1 + C2 * B ^ d2 := add_le_add (hp B hB x hx) (hq B hB x hx)
      _ ≤ C1 * B ^ (d1 + d2) + C2 * B ^ (d1 + d2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (C1 + C2) * B ^ (d1 + d2) := by ring
  | mul_X p s hp =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    refine ⟨C1, d1 + 1, h1, fun B hB x hx => ?_⟩
    rw [map_mul, aeval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hp B hB x hx) (hx s) (norm_nonneg _)
      (mul_nonneg h1 (pow_nonneg (by linarith) _))

theorem poly_bound_fam {κ σ : Type} [Fintype κ] (P : κ → MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ∀ k, ‖aeval x (P k)‖ ≤ C * B ^ d := by
  choose C d hC h using fun k => poly_bound (P k)
  refine ⟨∑ k, C k, ∑ k, d k, Finset.sum_nonneg fun k _ => hC k, fun B hB x hx k => ?_⟩
  exact (h k B hB x hx).trans (mul_le_mul
    (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ k))
    (pow_le_pow_right₀ hB (Finset.single_le_sum (fun k _ => Nat.zero_le (d k)) (Finset.mem_univ k)))
    (pow_nonneg (by linarith) _) (Finset.sum_nonneg fun k _ => hC k))

variable {ι : Type} {m : ι → ℕ}

def adjPoly (m : ι → ℕ) (w : EntIx m) : MvPolynomial (EntIx m) ℤ :=
  Matrix.adjugate (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)) w.2.1 w.2.2

theorem aeval_adjPoly (A : Mat m ℂ) (w : EntIx m) :
    aeval (fun u : EntIx m => A u.1 u.2.1 u.2.2) (adjPoly m w) = (A w.1).adjugate w.2.1 w.2.2 := by
  have e : (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)).map
      (aeval fun u : EntIx m => A u.1 u.2.1 u.2.2) = A w.1 := by
    ext p q; simp
  rw [← e]
  exact congrFun (congrFun (RingHom.map_adjugate (aeval (R := ℤ) fun u : EntIx m => A u.1 u.2.1 u.2.2).toRingHom _) w.2.1) w.2.2

variable [Fintype ι]

def lieCoeff (ρ : PolyRep m) (i j : Fin ρ.M) (w : EntIx m) : ℂ :=
  aeval (fun u : EntIx m => (1 : Mat m ℂ) u.1 u.2.1 u.2.2) (pderiv w (ρ.ent i j))

theorem lie_apply (ρ : PolyRep m) (A : Mat m ℂ) (i j : Fin ρ.M) :
    ρ.lie A i j = ∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2 := rfl

def lieNorm (ρ : PolyRep m) : ℝ := ∑ i, ∑ j, ∑ w, ‖lieCoeff ρ i j w‖

theorem lieNorm_nonneg (ρ : PolyRep m) : 0 ≤ lieNorm ρ := by unfold lieNorm; positivity

theorem norm_lie_mul_le (ρ : PolyRep m) (A : Mat m ℂ) {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ w : EntIx m, ‖A w.1 w.2.1 w.2.2‖ * t ≤ c) (i j : Fin ρ.M) :
    ‖ρ.lie A i j‖ * t ≤ lieNorm ρ * |c| := by
  have h1 : ‖ρ.lie A i j‖ * t ≤ ∑ w, ‖lieCoeff ρ i j w‖ * |c| := by
    rw [lie_apply]
    calc ‖∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖ * t
        ≤ (∑ w, ‖lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖) * t :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht
      _ = ∑ w, ‖lieCoeff ρ i j w‖ * (‖A w.1 w.2.1 w.2.2‖ * t) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun w _ => ?_; rw [norm_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left ((h w).trans (le_abs_self c)) (norm_nonneg _)
  refine h1.trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg c)
  unfold lieNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖lieCoeff ρ i j w‖)
    (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ∑ w, ‖lieCoeff ρ i j w‖) (fun j _ => by positivity)
    (Finset.mem_univ j)

theorem lie_neg (ρ : PolyRep m) (A : Mat m ℂ) : ρ.lie (fun τ => -A τ) = -ρ.lie A := by
  ext i j; simp [lie_apply, Finset.sum_neg_distrib]

theorem lie_sub (ρ : PolyRep m) (A B : Mat m ℂ) : ρ.lie (fun τ => A τ - B τ) = ρ.lie A - ρ.lie B := by
  ext i j; simp [lie_apply, mul_sub, Finset.sum_sub_distrib]

theorem mdel_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdel (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdel (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdel_apply, lie_apply]
  rw [del_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [del_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem mdbar_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdbar (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdbar (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdbar_apply, lie_apply]
  rw [dbar_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem poinWt_nonneg {n : ℕ} (S : Finset (Fin n)) (v : V n) (a : Fin n) : 0 ≤ poinWt S v a := by
  unfold poinWt; split_ifs <;> positivity

end GlobalTheory.RepBound

namespace GlobalTheory.RepBound

theorem le_mul_pow_of_le {x K c' L : ℝ} {e N' : ℕ} (hx : x ≤ K * L ^ e) (hK : K ≤ c') (hK0 : 0 ≤ K)
    (hL : 1 ≤ L) (he : e ≤ N') : x ≤ c' * L ^ N' :=
  hx.trans (mul_le_mul hK (pow_le_pow_right₀ hL he) (pow_nonneg (by linarith) _) (hK0.trans hK))

theorem goodBound_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ),
    ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) →
      (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) →
        GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  intro ι _ m ρ c N
  obtain ⟨C1, d1, hC1, h1⟩ := poly_bound_fam (fun p : Fin ρ.M × Fin ρ.M => ρ.ent p.1 p.2)
  obtain ⟨C2, d2, hC2, h2⟩ := poly_bound ρ.ent.det
  obtain ⟨C3, d3, hC3, h3⟩ := poly_bound_fam (adjPoly m)
  have hc₁ : 1 ≤ max c 1 := le_max_right _ _
  have hc₀ : 0 ≤ max c 1 := by linarith
  have hK1 : 0 ≤ C1 * max c 1 ^ d1 := mul_nonneg hC1 (pow_nonneg hc₀ _)
  have hK2 : 0 ≤ C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) :=
    mul_nonneg (mul_nonneg hC2 (pow_nonneg (by linarith) _)) (pow_nonneg hc₀ _)
  have hK3 : 0 ≤ lieNorm ρ * |c| := mul_nonneg (lieNorm_nonneg ρ) (abs_nonneg c)
  refine ⟨C1 * max c 1 ^ d1 + C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) + lieNorm ρ * |c|,
    N * d1 + N * ((d3 + 1) * d2), ?_⟩
  intro n S G v hG hdet hL hB
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := by linarith
  set B := max c 1 * L ^ N with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hc₁ (one_le_pow₀ hL)
  have hx : ∀ w : EntIx m, ‖G v w.1 w.2.1 w.2.2‖ ≤ B := fun w =>
    ((hB w.1).entry w.2.1 w.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
  have hu : ∀ τ, IsUnit (G v τ).det := fun τ => isUnit_iff_ne_zero.2 (hdet τ)
  have hcv := (GlobalTheory.T.chernConnection_curvature_polyRep_eval ι m ρ n G v hG hdet).1
  have hcvE : ∀ ξ, (fun u => conn (fun w => ρ.ev (G w)) u ξ) =ᶠ[𝓝 v]
      (fun u => ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) := fun ξ => hcv.mono fun u hu => hu ξ
  have hc1 : ∀ τ ξ, MContDiffAt 1 (fun u => conn (fun w => G w τ) u ξ) v :=
    fun τ ξ => (hG τ).conn (hu τ) (by norm_num) ξ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change ‖ρ.ev (G v) i j‖ ≤ _
    have := h1 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx (i, j)
    refine le_mul_pow_of_le (K := C1 * max c 1 ^ d1) (e := N * d1) ?_ (by linarith) hK1 hL (by omega)
    refine this.trans_eq ?_
    rw [hBdef, mul_pow, ← pow_mul]; ring
  · change ‖(ρ.ev (G v)).det‖⁻¹ ≤ _
    set Gi : Mat m ℂ := fun τ => (G v τ)⁻¹ with hGi
    have hmul : ρ.ev (G v) * ρ.ev Gi = 1 := by
      have e : G v * Gi = 1 := funext fun τ => Matrix.mul_nonsing_inv _ (hu τ)
      rw [PolyRep.ev, PolyRep.ev, ← ρ.mul ℂ, e]
      exact ρ.one ℂ
    have hdm : (ρ.ev (G v)).det * (ρ.ev Gi).det = 1 := by rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hinv : ‖(ρ.ev (G v)).det‖⁻¹ = ‖(ρ.ev Gi).det‖ := by
      rw [← norm_inv, inv_eq_of_mul_eq_one_right hdm]
    have hpoly : (ρ.ev Gi).det = aeval (fun w : EntIx m => Gi w.1 w.2.1 w.2.2) ρ.ent.det :=
      (AlgHom.map_det _ _).symm
    have hy : ∀ w : EntIx m, ‖Gi w.1 w.2.1 w.2.2‖ ≤ (C3 + 1) * B ^ (d3 + 1) := by
      intro w
      have ha := h3 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx w
      rw [aeval_adjPoly (G v) w] at ha
      have hd : ‖(G v w.1).det‖⁻¹ ≤ B :=
        ((hB w.1).det).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
      have e : Gi w.1 w.2.1 w.2.2 = ((G v w.1).det)⁻¹ * (G v w.1).adjugate w.2.1 w.2.2 := by
        simp [hGi, Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e, norm_mul, norm_inv]
      have hBd : 0 ≤ B ^ d3 := pow_nonneg (by linarith) _
      calc ‖(G v w.1).det‖⁻¹ * ‖(G v w.1).adjugate w.2.1 w.2.2‖ ≤ B * (C3 * B ^ d3) :=
            mul_le_mul hd ha (norm_nonneg _) (by linarith)
        _ ≤ (C3 + 1) * B ^ (d3 + 1) := by
            rw [pow_succ]; nlinarith [mul_nonneg hBd (by linarith : (0:ℝ) ≤ B)]
    have hB2 : 1 ≤ (C3 + 1) * B ^ (d3 + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hB1)
    have hd2 := h2 _ hB2 _ hy
    rw [hinv, hpoly]
    refine le_mul_pow_of_le (K := C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2))
      (e := N * ((d3 + 1) * d2)) ?_ (by linarith) hK2 hL (by omega)
    refine hd2.trans_eq ?_
    rw [hBdef, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring
  · intro a i j
    change ‖conn (fun u => ρ.ev (G u)) v (coordVec a) i j‖ * poinWt S v a ≤ _
    have e := (hcvE (coordVec a)).self_of_nhds
    simp only at e
    rw [e]
    exact (norm_lie_mul_le ρ _ (poinWt_nonneg S v a) (fun w => (hB w.1).form a w.2.1 w.2.2) i j).trans
      (by linarith)
  · intro a b i j
    have e : curv (fun u => ρ.ev (G u)) v (coordVec a) (coordVec b) =
        ρ.lie (fun τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)) := by
      rw [curv, mdbar_congr (hcvE (coordVec a)), mdbar_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_neg]
      rfl
    rw [e]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).dbar a b w.2.1 w.2.2) i j).trans (by linarith)
  · intro a b i j
    rw [mdel_congr (hcvE (coordVec b)), mdel_congr (hcvE (coordVec a)),
      mdel_lie ρ (fun τ => hc1 τ (coordVec b)), mdel_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_sub]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).del a b w.2.1 w.2.2) i j).trans (by linarith)

end GlobalTheory.RepBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydisc
section
open GlobalTheory.ShFam.Hor

namespace GlobalTheory

theorem periodVec_im_dot {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im
      = dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
  simp [dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum, Complex.mul_im]

theorem periodVec_norm_exp_le {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : (M.map Complex.im).PosDef)
    (v : Fin g → ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ))))‖ ≤ 1 := by
  have h1 : 0 ≤ dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
    have := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
    simpa using this
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).re
      = -(2 * Real.pi) * (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, periodVec_im_dot]
  have := Real.pi_pos
  nlinarith

end GlobalTheory

namespace GlobalTheory

theorem periodVec_extends : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  intro n a g ha ρ₁ τ B v hρ0 hρ1 hdiff hpos hmono hm
  let vC : Fin g → ℂ := fun i => (v i : ℂ)
  let m : Fin a → ℤ := fun k => dotProduct v ((B k).mulVec v)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcd : ∀ x : ℂ, 2 * Real.pi * Complex.I * (x / (2 * Real.pi * Complex.I)) = x := fun x => by
    field_simp
  let h : (Fin n → ℂ) → ℂ := fun s => dotProduct vC ((τ s).mulVec vC) -
    ∑ k, s (Fin.castLE ha k) * ((m k : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
  have hdh : DifferentiableOn ℂ h
      {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁} := by
    apply DifferentiableOn.sub
    · simp only [dotProduct, Matrix.mulVec]
      apply DifferentiableOn.fun_sum; intro i _
      apply DifferentiableOn.mul (differentiableOn_const _)
      apply DifferentiableOn.fun_sum; intro j _
      exact (hdiff i j).mul (differentiableOn_const _)
    · apply DifferentiableOn.fun_sum; intro k _
      simp only [div_eq_mul_inv]
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.mul_const
      exact differentiableOn_pi.mp differentiableOn_id (Fin.castLE ha k)
  have hQ : ∀ k : Fin a, dotProduct vC (((B k).map (Int.cast : ℤ → ℂ)).mulVec vC) = ((m k : ℤ) : ℂ) := by
    intro k
    simp [vC, m, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  have hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
      ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s := by
    intro s hs hb k hk
    obtain ⟨k', rfl⟩ : ∃ k' : Fin a, Fin.castLE ha k' = k := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    have hτ := hmono s hs hb k'
    simp only [h]
    rw [hτ, Matrix.add_mulVec, dotProduct_add, hQ k']
    have hsum : ∑ j, (s + Pi.single (Fin.castLE ha k') (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE ha j)
        * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
        = ∑ j, s (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) + ((m k' : ℤ) : ℂ) := by
      simp only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]
      congr 1
      simp only [Pi.single_apply, (Fin.castLE_injective ha).eq_iff, ite_mul, zero_mul, ite_div, zero_div,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
    rw [hsum]; ring
  obtain ⟨H, hHd, hHe⟩ := GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover n a ρ₁ h hρ0 hρ1 hdh hinv
  let m' : Fin n → ℕ := fun j => if hj : (j : ℕ) < a then (m ⟨j, hj⟩).toNat else 0
  have hm0 : ∀ k, (((m k).toNat : ℕ) : ℂ) = ((m k : ℤ) : ℂ) := fun k => by
    have := Int.toNat_of_nonneg (hm k)
    exact_mod_cast this
  have hbound : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k ≤ 1 := by
    intro z hz hz0
    let s : Fin n → ℂ := fun j => if (j : ℕ) < a then Complex.log (z j) else z j
    have hzj : ∀ j, ‖z j‖ < ρ₁ := fun j =>
      lt_of_le_of_lt (norm_le_pi_norm z j) (by simpa using hz)
    have hls : logExp a s = z := by
      funext j; simp only [logExp, s]; split_ifs with hj
      · exact Complex.exp_log (hz0 j hj)
      · rfl
    have hsD : s ∈ logDom n a := by
      simp only [logDom, Set.mem_setOf_eq]
      intro j; simp only [s]; split_ifs with hj
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 (hz0 j hj)) (lt_of_lt_of_le (hzj j) hρ1)
      · exact lt_of_lt_of_le (hzj j) hρ1
    have hb' : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by rw [hls]; exact hz
    have hHz : h s = H z := by rw [hHe s hsD hb', hls]
    have hprod : ∏ j, (z j) ^ m' j = ∏ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat := by
      symm
      apply Finset.prod_of_injOn (Fin.castLE ha)
      · intro x _ y _ hxy; exact Fin.castLE_injective ha hxy
      · intro x _; simp
      · intro j _ hj
        have : ¬ (j : ℕ) < a := by
          intro hlt; apply hj; exact ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩
        simp [m', this]
      · intro k _; simp [m', Fin.coe_castLE, k.isLt]
    have hexp : ∀ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat
        = Complex.exp (s (Fin.castLE ha k) * ((m k : ℤ) : ℂ)) := by
      intro k
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
      rw [mul_comm, ← hm0 k, Complex.exp_nat_mul]
      congr 1
      simp only [s, if_pos hk]; exact (Complex.exp_log (hz0 _ hk)).symm
    calc ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k
        = ‖Complex.exp (2 * Real.pi * Complex.I * h s) * ∏ k, z k ^ m' k‖ := by
          rw [norm_mul, norm_prod, hHz]; simp only [norm_pow]
      _ = ‖Complex.exp (2 * Real.pi * Complex.I * dotProduct vC ((τ s).mulVec vC))‖ := by
          rw [hprod, Finset.prod_congr rfl (fun k _ => hexp k), ← Complex.exp_sum, ← Complex.exp_add]
          congr 2
          simp only [h]
          rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hcd _)]
          ring
      _ ≤ 1 := periodVec_norm_exp_le _ (hpos s hsD hb').2 v
  obtain ⟨F, hFd, hFe⟩ := GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes n a ρ₁ H m' hρ0 hHd hbound
  refine ⟨F, hFd, fun s hs hb => ?_⟩
  rw [hFe _ hb (fun k hk => by simp [logExp, hk, Complex.exp_ne_zero])]
  exact hHe s hs hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevForms

theorem typeSpF_finiteDimensional : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
    FiniteDimensional K ↥(NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ hJ
  classical
  obtain ⟨N, hN, hNJ⟩ := hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  obtain ⟨Jc, hJc⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let Φ : ↥(NX.TypeSpF L n K ρ J χ) →ₗ[K] (↥(T ×ˢ Jc) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJc u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  obtain ⟨hκJ, hκ1⟩ := hNJ κ hκ
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 ⟨κ, hκJ⟩, hκ1, f.2.1 γ, h0, map_zero, Units.val_one, one_smul]

theorem levDatum_forms : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : SideA D cf jE) (S : RatDat D.ntw) (In : RatIn D S)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    (∀ v, NG.OverPl (Pq v) v) →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    ∀ (wt : WtData D T), (∀ i j b, 1 ≤ j → j ≤ D.R.m → (wt.rhoW i j b).IsIrreducible ∧
      NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b)) →
    ∀ (hE : IsEmpty D.nd.Loc) (F : TwF T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m →
      Formalism.MainNotions.NAdm.TWSet (T.ntw hE F (TwL.empty T)) i Q →
      (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) →
      IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) → AntiHom T.cc ψ → (∀ σ, ∃ N : ℕ, ψ σ ^ (T.l i ^ N) = 1) →
      (∀ P, P ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, ψ σ = 1) →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) := by
  intro hA D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt hwt hE F i j b k Q ψ hj1 hj2 hQ hQ2 hopen hanti hl hunr
  classical
  have hQs : ∀ P ∈ Q, IsSplitPl D.host P := fun P hP => (hQ P hP).1
  have hQl : ∀ P ∈ Q, P ∉ placesOver D.host.E (T.l i) := fun P hP => (hQ P hP).2
  have hDs : ∀ P ∈ T.pD i, IsSplitPl D.host P := by
    intro P hP
    have h := T.pD_eq i
    have hP' : P ∈ placesOver D.host.E (if T.l i = D.host.pde then D.host.pde' else D.host.pde) := by
      rw [← h]; exact hP
    split_ifs at hP' with hh
    · exact hsplit P (Or.inr hP')
    · exact hsplit P (Or.inl hP')
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.auxiliaryPrimePlaces_nonempty D T i
  haveI : Nonempty (SplitPlace D.host.E) := ⟨(GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P₀ (hDs P₀ hP₀)).choose⟩
  let sp : PlE D.host → SplitPlace D.host.E := fun P =>
    if h : IsSplitPl D.host P then (GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P h).choose else Classical.arbitrary _
  have hsp : ∀ P, IsSplitPl D.host P → (sp P).w = P := fun P h => by
    simp only [sp, dif_pos h]; exact (GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P h).choose_spec
  have hspw : ∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P := by
    rintro P (h | h | ⟨kv, rfl⟩)
    · exact hsp P (hQs P (qpOf_sub D Pq Q h))
    · exact hsp P (hDs P (qpOf_sub D Pq _ h))
    · exact hsp _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D kv.1 kv.2)
  obtain ⟨hv, hdisj1, hdisj2, hpG⟩ := GlobalTheory.T.split_places_avoid_auxiliary D T i Q Pq sp hPq hQs hQ2 hDs hspw
  let redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1) := fun kv =>
    (GlobalTheory.T.exists_residueHom_zmod_at_typePlace D kv (sp (NX.pG D kv)) (hspw _ (Or.inr (Or.inr ⟨kv, rfl⟩)))).some
  have hψt := fun P (hP : P ∈ qpOf D Pq Q) =>
    GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character ψ P 1 (T.l i) hopen (by simpa [placesOver] using hQl P (qpOf_sub D Pq Q hP)) (fun A _ σ _ => hl σ)
  have hδt := fun P (hP : P ∈ qpOf D Pq (T.pD i)) =>
    GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character (T.delta i) P (if b then 1 else -1) 15 (T.delta_open i) (GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow D T i P (qpOf_sub D Pq _ hP)).1
      (GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow D T i P (qpOf_sub D Pq _ hP)).2
  obtain ⟨J, χ, hJo, hhyp, hJm, hchi⟩ := GlobalTheory.T.exists_levelGroup_with_character_at_type_places D T In.θ i j b k Q ψ (qpOf D Pq Q) (qpOf D Pq (T.pD i)) sp redG
    hspw hv hdisj1 hdisj2 hpG (qpOf_sub D Pq Q) (qpOf_sub D Pq _) hψt hδt
  obtain ⟨hQc, hQn⟩ := GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once D Pq hPq Q hQs
  obtain ⟨hDc, hDn⟩ := GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once D Pq hPq (T.pD i) hDs
  refine ⟨⟨J, χ, qpOf D Pq Q, qpOf D Pq (T.pD i), sp, redG⟩,
    ⟨hJo, hhyp, rfl, rfl, qpOf_sub D Pq Q, hQc, hQn, qpOf_sub D Pq _, hDc, hDn, hspw, hJm, hchi⟩, ?_⟩
  exact typeSpF_finiteDimensional D.host.E D.R.nV _ (rhoKT D T wt i j b k) J χ hJo

end GlobalTheory.LevForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ en₀ en₁ : En Dw.mult, en₁.1 = en₀.1 + 1 → ∃ (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M en₀.1 + 1)) (q₁ : Fin L'.n → Fin (plN M en₁.1 + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g en₀ en₁ L' ix q₀ q₁ r := by
  first | exact @GlobalTheory.FlagEmb.QuotLine.exists_isLine | exact GlobalTheory.FlagEmb.QuotLine.exists_isLine | (intros; apply GlobalTheory.FlagEmb.QuotLine.exists_isLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_gluing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] a i (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k), spMap ψ ≫ (aff i).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π → ∀ en : En Dw.mult, ∃ hu, spMap φ ≫ Z.chart a ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) (plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1) hu := by
  first | exact @GlobalTheory.FlagEmb.PlkPt.plk_pt | exact GlobalTheory.FlagEmb.PlkPt.plk_pt | (intros; apply GlobalTheory.FlagEmb.PlkPt.plk_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_base_and_normal_coordinate_ring : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  first | exact @GlobalTheory.FlagEmb.cell_smooth_normal | exact GlobalTheory.FlagEmb.cell_smooth_normal | (intros; apply GlobalTheory.FlagEmb.cell_smooth_normal <;> assumption)
end


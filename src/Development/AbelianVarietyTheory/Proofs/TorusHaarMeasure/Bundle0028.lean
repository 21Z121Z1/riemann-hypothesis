import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BoundOfIneqs
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ProperFromMinimum

theorem bound_of_ineqs {K K' c i δ S n p : ℝ} {a : ℕ} (hδ : 0 < δ) (hac : (a : ℝ) * c < i)
    (hS : 0 ≤ S) (h1 : Real.exp (-(2 * c * p)) ≤ K * S) (h2 : n ≤ K' * Real.exp (-(2 * i * p)))
    (h3 : δ * S ^ a ≤ n) : p ≤ K ^ a * K' / δ / (2 * (i - a * c)) := by
  have hK : 0 ≤ K := by
    by_contra hK
    have : K * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hK)) hS
    linarith [Real.exp_pos (-(2 * c * p))]
  have hKa : 0 ≤ K ^ a := pow_nonneg hK a
  have e1 : Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * S ^ a := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 a
  have e2 : δ * Real.exp (-(2 * c * p)) ^ a ≤ K ^ a * K' * Real.exp (-(2 * i * p)) := by
    calc δ * Real.exp (-(2 * c * p)) ^ a ≤ δ * (K ^ a * S ^ a) :=
          mul_le_mul_of_nonneg_left e1 hδ.le
      _ = K ^ a * (δ * S ^ a) := by ring
      _ ≤ K ^ a * (K' * Real.exp (-(2 * i * p))) := mul_le_mul_of_nonneg_left (h3.trans h2) hKa
      _ = _ := by ring
  have e3 : Real.exp (-(2 * c * p)) ^ a =
      Real.exp (2 * (i - a * c) * p) * Real.exp (-(2 * i * p)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [e3, ← mul_assoc] at e2
  have e4 : δ * Real.exp (2 * (i - a * c) * p) ≤ K ^ a * K' :=
    le_of_mul_le_mul_right e2 (Real.exp_pos _)
  have e5 : 2 * (i - a * c) * p ≤ Real.exp (2 * (i - a * c) * p) := by
    linarith [Real.add_one_le_exp (2 * (i - a * c) * p)]
  have hd : 0 < 2 * (i - a * c) := by linarith
  rw [le_div_iff₀ hd, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_left e5 hδ.le]

theorem exists_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (L eW : Wt X.Ψ r) (N a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ), (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x) → InterpolationModelInequalities X L eW w et c i ph → (a : ℝ) * c < i → ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by
  intro E _ _ _ r X L eW N a w et c i ph hph hI hac δ hδ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hsub : Subsingleton (Frame X.Ψ 0) := inferInstance
    refine ⟨X.dom, (Set.subsingleton_of_subsingleton).finite.isCompact, subset_rfl, ?_⟩
    intro x hx _
    refine ⟨1, X.Γ.one_mem, x, fun τ => ⟨(hx τ).1, fun a => a.elim0⟩, ?_⟩
    rwa [Subsingleton.elim (lact 1 (rmul x x)) x]
  obtain ⟨ca, ε0, hca, hε0, hlow⟩ := hph
  obtain ⟨⟨K, hK⟩, K', hK'⟩ := hI
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max (K ^ a * K' / δ / (2 * (i - a * c))) 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hε : 0 < min ε0 (Real.sqrt (ca / B)) := lt_min hε0 (Real.sqrt_pos.2 (div_pos hca hB0))
  obtain ⟨C, hC, hCd, hmeet⟩ := reductionTheory_holds (E := E) r X _ hε
  refine ⟨C, hC, hCd, fun x hx h3 => hmeet x hx ?_⟩
  by_cases hsmall : X.la1 x < ε0
  · refine (min_le_right _ _).trans ?_
    have hpos : 0 < X.la1 x := la1_pos_of_mem_dom X hr hx
    have hp : ph x ≤ B := by
      rw [hB]
      exact (bound_of_ineqs hδ hac (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hK x hx) (hK' x hx)
        h3).trans (le_max_left _ _)
    have h4 : ca / X.la1 x ^ 2 ≤ B := (hlow x hx hsmall).trans hp
    rw [div_le_iff₀ (by positivity)] at h4
    apply Real.sqrt_le_iff.2
    refine ⟨hpos.le, ?_⟩
    rw [div_le_iff₀ hB0]
    linarith
  · exact (min_le_left _ _).trans (not_lt.1 hsmall)

end GlobalTheory.ProperFromMinimum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahlerStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_bound_orthonormal_frame_mahler : (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x → ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  first | exact @GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | exact GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | (intros; apply GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroupStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_drift_function_realUnitaryGroup : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  first | exact @GlobalTheory.DriftUnitary.exists_drift_function | exact GlobalTheory.DriftUnitary.exists_drift_function | (intros; apply GlobalTheory.DriftUnitary.exists_drift_function <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumBoundedBelow
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix

namespace GlobalTheory.TwoLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def leviCol (X : Data E 2) (x0 : Frame X.Ψ 2) (τ : X.Ψ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((Real.log (colSq (cpt X x0 w) τ) : ℝ) : ℂ)) z ξ).re

theorem wd_affine {n : ℕ} (c d : ℂ) (k j : Fin n) (z : V n) :
    wd n j (fun w : V n => c + d * w k) z = if j = k then d else 0 := by
  have h : HasFDerivAt (fun w : V n => c + d * w k)
      (d • (EuclideanSpace.proj k : V n →L[ℂ] ℂ)) z :=
    ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).hasFDerivAt.const_mul d).const_add c
  rw [wd_of_differentiableAt h.differentiableAt, h.fderiv]
  simp [bas, eq_comm]

theorem leviCol_eq (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    0 ≤ leviCol X x0 τ z ξ ∧ (ξ (idx X τ) ≠ 0 → 0 < leviCol X x0 τ z ξ) := by
  let g : Fin 2 → V (nd X) → ℂ := fun a w => x0 τ a 0 + x0 τ a 1 * w (idx X τ)
  have hs : ∀ w, colSq (cpt X x0 w) τ = sqNorm fun a => g a w := fun w => by
    simp [colSq, sqNorm, compact_frame_first_column, g, Complex.normSq_eq_norm_sq]
  have hpos : 0 < sqNorm fun a => g a z := hs z ▸ colSq_pos (by rwa [det_cpt])
  have hne : (fun a => g a z) ≠ 0 := fun h0 => by rw [h0] at hpos; simp [sqNorm] at hpos
  have hcd : ∀ a, ContDiffAt ℂ 2 (g a) z := fun a =>
    (contDiff_const.add (contDiff_const.mul
      (EuclideanSpace.proj (idx X τ) : V (nd X) →L[ℂ] ℂ).contDiff)).contDiffAt
  have hL := leviLogNormSq (nd X) 2 g z ξ hcd hne
  have hJ : wJac (nd X) 2 g z *ᵥ ξ = fun a => x0 τ a 1 * ξ (idx X τ) := by
    funext a
    simp [wJac, Matrix.mulVec, dotProduct, g, wd_affine]
  unfold leviCol
  simp only [hs]
  rw [hL, Complex.ofReal_re, hJ]
  refine ⟨div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) hpos.le, fun hξ =>
    div_pos (sqNorm_pos fun h0 => ?_) hpos⟩
  rw [projPerp_mulVec] at h0
  set c := ((sqNorm fun a => g a z : ℝ) : ℂ)⁻¹ * (star (fun a => g a z) ⬝ᵥ fun a => x0 τ a 1 * ξ (idx X τ))
  have e0 : x0 τ 0 1 * ξ (idx X τ) - c * (x0 τ 0 0 + x0 τ 0 1 * z (idx X τ)) = 0 := congrFun h0 0
  have e1 : x0 τ 1 1 * ξ (idx X τ) - c * (x0 τ 1 0 + x0 τ 1 1 * z (idx X τ)) = 0 := congrFun h0 1
  rw [det_mat] at h
  have hc : c = 0 := by
    apply (mul_eq_zero_iff_right h).1
    linear_combination x0 τ 0 1 * e1 - x0 τ 1 1 * e0
  apply mul_ne_zero h hξ
  rw [hc] at e0 e1
  linear_combination x0 τ 0 0 * e1 - x0 τ 1 0 * e0

theorem logCol_cd (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) : ContDiffAt ℝ 2 (fun w => Real.log (colSq (cpt X x0 w) τ)) z := by
  refine ContDiffAt.log ?_ (colSq_pos (by rwa [det_cpt])).ne'
  have hc : ∀ a, ContDiffAt ℝ 2 (fun w => ‖cpt X x0 w τ a 0‖ ^ 2) z := fun a =>
    (((IW.cpt_entry_cd X x0 τ a 0).restrict_scalars ℝ).of_le HE.two_le_inf).contDiffAt.norm_sq ℂ
  exact (hc 0).add (hc 1)

omit [NumberField E] [IsCMField E] in
theorem univ_two {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ} (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) [DecidableEq Ψ] :
    (Finset.univ : Finset Ψ) = {τ₁, τ₂} := by
  ext τ; simpa using hall τ

omit [NumberField E] [IsCMField E] in
theorem prod_two {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ} (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {M : Type*} [CommMonoid M] (f : Ψ → M) : ∏ τ, f τ = f τ₁ * f τ₂ := by
  classical
  rw [univ_two hall, Finset.prod_pair hne]

omit [NumberField E] [IsCMField E] in
theorem sum_two {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ} (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {M : Type*} [AddCommMonoid M] (f : Ψ → M) : ∑ τ, f τ = f τ₁ + f τ₂ := by
  classical
  rw [univ_two hall, Finset.sum_pair hne]

theorem leviM_phla {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) {τ₁ τ₂ : X.Ψ} (hne : τ₁ ≠ τ₂)
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom) (la : Wt X.Ψ 2)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (phla X la) x0 z ξ = (la τ₁ 0 - la τ₁ 1 : ℝ) * leviCol X x0 τ₁ z ξ +
      (la τ₂ 0 - la τ₂ 1 : ℝ) * leviCol X x0 τ₂ z ξ := by
  have h1 := logCol_cd X (hx τ₁).1 z
  have h2 := logCol_cd X (hx τ₂).1 z
  unfold leviM leviCol
  simp only [phla_cpt hG hp hx, sum_two hne hall]
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add ((contDiffAt_const.mul h1).add contDiffAt_const)
    ((contDiffAt_const.mul h2).add contDiffAt_const), Y.leviV_const_mul h1, Y.leviV_const_mul h2,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem leviCol_add_pos {X : Data E 2} {τ₁ τ₂ : X.Ψ}
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom)
    (z : V (nd X)) {ξ : Fin (nd X) → ℂ} (hξ : ξ ≠ 0) :
    0 < leviCol X x0 τ₁ z ξ + leviCol X x0 τ₂ z ξ := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hξ
  obtain ⟨τ, rfl⟩ := idx_surjective X k
  have h1 := leviCol_eq X (hx τ₁).1 z ξ
  have h2 := leviCol_eq X (hx τ₂).1 z ξ
  rcases hall τ with rfl | rfl
  · linarith [h1.2 hk, h2.1]
  · linarith [h2.2 hk, h1.1]

def idF (Ψ : Finset (E →+* ℂ)) : Frame Ψ 2 := fun _ => ![![1, 0], ![0, 1]]

def swF (Ψ : Finset (E →+* ℂ)) : Frame Ψ 2 := fun _ => ![![0, 1], ![1, 0]]

theorem isOrth_idF {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) : IsOrth X (idF X.Ψ) := by
  intro τ
  ext a b
  rw [hG, hp, gram_one]
  fin_cases a <;> fin_cases b <;> simp [idF, sgn]

theorem first_minimum_bounded_below {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, ε ≤ X.la1 x := by
  obtain ⟨h1, h2, h3⟩ := ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames 2 X two_pos
  have hsub : {x : Frame X.Ψ 2 | IsOrth X x} ⊆ X.dom := fun x hx => IW.orth_mem_dom X x hx
  obtain ⟨y, hy, hmin⟩ := (isCompact_orth hG hp).exists_isMinOn ⟨_, isOrth_idF hG hp⟩ (h2.mono hsub)
  refine ⟨_, h3 y (hsub hy), fun x hx => ?_⟩
  obtain ⟨x1, ho, b, hb, rfl⟩ := ortho_holds 2 X x hx
  have := h1 1 X.Γ.one_mem x1 (hsub ho) b hb
  rw [lact_one'] at this
  rw [this]
  exact hmin ho

end GlobalTheory.TwoLines
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonalStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.leviForm_weightMetric_orthonormal_diagonal : (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) := by
  first | exact @GlobalTheory.LeviZero.leviZero | exact GlobalTheory.LeviZero.leviZero | (intros; apply GlobalTheory.LeviZero.leviZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.exp_neg_phla {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by
  have hpos := _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) + Real.log (X.nfac la x) by
    ring, Real.exp_add, Real.exp_log hpos]
  ring

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_rmul (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.pnorm la P x :=
  _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_lact (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = X.pnorm la P x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hN
  change ‖P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x)‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = ‖P x‖ * X.nfac la x
  rw [hP.2.2 γ hγ x hx, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hN r X la γ hγ x hx]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.measurable_cut {f : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ}
    (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator fun x => ENNReal.ofReal (f x)) := by
  have hc : ContinuousOn (fun x => ((Real.sqrt (f x) : ℝ) : ℂ)) X.dom :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hf)
  have key : ∀ y, ENNReal.ofReal (‖((Real.sqrt (f y) : ℝ) : ℂ)‖ ^ 2) = ENNReal.ofReal (f y) := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rcases le_total 0 (f y) with h | h
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero'.mpr h, ENNReal.ofReal_of_nonpos h]
      simp
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF_meas X (W := 1) hc measurable_one
  convert hm using 1
  funext y
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF
  simp only [Pi.one_apply, mul_one]
  by_cases hy : y ∈ X.dom
  · rw [Set.indicator_of_mem hy, Set.piecewise_eq_of_mem _ _ _ hy, key]
  · rw [Set.indicator_of_notMem hy, Set.piecewise_eq_of_notMem _ _ _ hy]
    rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.exists_sum_le {N : ℕ} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : Fin N → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : ∀ k, X.IsBddSec la (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨1 + ∑ k, C k ^ 2, by positivity, fun x hx => ?_⟩
  have hle : ∀ k, X.pnorm la (P k) x ^ 2 ≤ C k ^ 2 := by
    intro k
    have h0 : 0 ≤ X.pnorm la (P k) x := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      exact mul_nonneg (norm_nonneg _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la).le
    exact pow_le_pow_left₀ h0 (hC k x hx) 2
  calc ∑ k, X.pnorm la (P k) x ^ 2 ≤ ∑ k, C k ^ 2 := Finset.sum_le_sum fun k _ => hle k
    _ ≤ 1 + ∑ k, C k ^ 2 := by linarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le {a C t : ℝ} (hC : 0 < C) (h : a ≤ C) (ht : 0 ≤ t) :
    ENNReal.ofReal (C ^ (-t)) ≤ ENNReal.ofReal a ^ (-t) := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha h (by linarith))
  · rw [ENNReal.ofReal_of_nonpos ha]
    rcases ht.lt_or_eq with ht | ht
    · rw [ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
    · subst ht
      simp

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)

theorem measurable_Wdiv : Measurable (Wdiv X Xa Fl n) := by
  have h1 := measurable_cut ((ExtFPf.nfac_contOn X Xa.Fp).pow 2)
  have h2 : Measurable (X.dom.indicator fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) :=
    measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (Xa.w_van k).1.1.1.1.continuousOn.norm.pow 2)
  have h3 : Measurable (X.dom.indicator fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) :=
    measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (Fl.s_van k).1.1.1.1.continuousOn.norm.pow 2)
  have h := (h1.mul (h2.pow_const (-(1 / 2 : ℝ)))).mul (h3.pow_const (-((n : ℝ) - 1 / 2)))
  convert h using 1
  funext x
  by_cases hx : x ∈ X.dom
  · rw [Wdiv_of_mem Xa Fl n hx, exp_neg_phla hx]
    simp only [Pi.mul_apply, Set.indicator_of_mem hx, Pi.pow_apply]
  · rw [Wdiv_of_notMem Xa Fl n hx]
    simp only [Pi.mul_apply, Set.indicator_of_notMem hx, zero_mul]

theorem Wdiv_rmul (hN : NfacRmulStatement (E := E)) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    Wdiv X Xa Fl n (rmul x b) =
      Wdiv X Xa Fl n x / ENNReal.ofReal (‖bchar (Xa.Fp + n • Xa.L) b‖ ^ 2) := by
  have hxb := OntoS.dom_rmul X hx hb
  have h0 : 0 < ‖bchar (Xa.Fp + n • Xa.L) b‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (OntoE.bchar_ne X _ hb)) 2
  rw [Wdiv_eq_pnorm Xa Fl n hxb, Wdiv_eq_pnorm Xa Fl n hx, exp_neg_phla hx, exp_neg_phla hxb,
    hN r X _ x hx b hb]
  simp only [fun k => pnorm_rmul hN (Xa.w_van k).1.1.1 hx hb,
    fun k => pnorm_rmul hN (Fl.s_van k).1.1.1 hx hb]
  rw [mul_pow, inv_pow, ENNReal.ofReal_mul (inv_nonneg.2 h0.le), ENNReal.ofReal_inv_of_pos h0,
    ENNReal.div_eq_inv_mul]
  simp only [mul_assoc]

theorem Wdiv_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wdiv X Xa Fl n (lact γ x) = Wdiv X Xa Fl n x := by
  have hxb := OntoS.dom_lact X hγ hx
  rw [Wdiv_eq_pnorm Xa Fl n hxb, Wdiv_eq_pnorm Xa Fl n hx, exp_neg_phla hx, exp_neg_phla hxb,
    hN r X _ γ hγ x hx]
  simp only [fun k => pnorm_lact hN (Xa.w_van k).1.1.1 hγ hx,
    fun k => pnorm_lact hN (Fl.s_van k).1.1.1 hγ hx]

theorem Wdiv_lower (hn : 1 ≤ n) : WLower X (Xa.Fp + n • Xa.L) (Wdiv X Xa Fl n) := by
  obtain ⟨A, hA, hAw⟩ := exists_sum_le fun k => (Xa.w_van k).1.1
  obtain ⟨B, hB, hBs⟩ := exists_sum_le fun k => (Fl.s_van k).1.1
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hA' := Real.rpow_pos_of_pos hA (-(1 / 2 : ℝ))
  have hB' := Real.rpow_pos_of_pos hB (-((n : ℝ) - 1 / 2))
  refine ⟨A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2)), mul_pos hA' hB', fun x hx => ?_⟩
  rw [Wdiv_eq_pnorm Xa Fl n hx, mul_comm, ← mul_assoc,
    ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) hA').le, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' (mul_le_mul' le_rfl (ofReal_rpow_neg_le hA (hAw x hx) (by norm_num)))
    (ofReal_rpow_neg_le hB (hBs x hx) hn')

theorem divMetric_of :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) →
      GlobalTheory.Up.DivMetric (E := E) := by
  intro h r X Xa Fl n hn
  exact ⟨⟨measurable_Wdiv Xa Fl n, fun x hx b hb => Wdiv_rmul Xa Fl n h.1 hx hb,
    fun γ hγ x hx => Wdiv_lact Xa Fl n h.2.1 hγ hx⟩, Wdiv_lower Xa Fl n hn,
    fun x hx hs => Wdiv_eq_exp Xa Fl n hx hs⟩

end GlobalTheory.Up.DivMetricPf
end


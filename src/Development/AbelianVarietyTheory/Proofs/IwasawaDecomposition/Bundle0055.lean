import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInductionStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTriangular_GL_complex_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) → (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) → (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) → ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  first | exact @GlobalTheory.lowerTriangular_GL_induction | exact GlobalTheory.lowerTriangular_GL_induction | (intros; apply GlobalTheory.lowerTriangular_GL_induction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedVacuumDeriv
section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.MovedVac

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

def omL (J : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).flip.comp (J.toContinuousLinearEquiv : V →L[ℝ] V)).flip

theorem omL_apply (x y : V) : omL J x y = omJ J x y := rfl

theorem omL_self (hJ : ∀ x, J (J x) = -x) (x : V) : omL J x x = 0 := by
  have := omJ_skew hJ x x
  rw [omL_apply]; linarith

theorem abs_omJ_le (x y : V) : |omJ J x y| ≤ ‖x‖ * ‖y‖ := by
  have := abs_real_inner_le_norm x (J y)
  rwa [J.norm_map] at this

theorem calc' (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) :
    (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧
    (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (omJ J w y : ℂ)) • ρ w f) ∧
    (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (omJ J v w : ℂ)) • ρ w f) :=
  have := DCalc.dH_calculus V B (omL J) ρ (omL_self hJ) h f hf
  ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩

theorem norm_sub_le (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (u z : V) :
    ‖ρ (u + z) f - ρ u f‖ ≤ ‖dH ρ z f‖ + π * (‖u‖ * ‖z‖) * ‖f‖ := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ρ (u + s • z) f) (fderiv ℝ (fun u => ρ u f) (u + s • z) z) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => u + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add u
    exact (ContDiff.differentiable hf (by simp) _).hasFDerivAt.comp_hasDerivAt s h2
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s : ℝ => ρ (u + s • z) f)
    (C := ‖dH ρ z f‖ + π * (‖u‖ * ‖z‖) * ‖f‖) (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => ?_)
  · simpa using this
  · have e : omJ J (u + s • z) z = omJ J u z := by
      rw [← omL_apply, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        omL_self hJ, smul_zero, add_zero, omL_apply]
    rw [(calc' hJ h hf).2.2.1, e]
    refine (_root_.norm_sub_le _ _).trans ?_
    rw [h.2.2.1, norm_smul, h.2.2.1]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have := abs_omJ_le (J := J) u z
    gcongr

theorem integrable_coef (h : IsHeis (omJ J) ρ) (f : B) {φ : V → ℂ} (hφ : Continuous φ) (K : ℝ) (n : ℕ)
    (hb : ∀ u, ‖φ u‖ ≤ K * ‖u‖ ^ n) : Integrable fun u => gau u • φ u • ρ u f := by
  refine Integrable.mono' (((Osc.integrable_pow_gau (V := V) n).const_mul K).mul_const ‖f‖)
    (continuous_gau.smul (hφ.smul (h.2.2.2 f))).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, norm_smul, h.2.2.1]
  calc ‖gau u‖ * (‖φ u‖ * ‖f‖) ≤ ‖gau u‖ * (K * ‖u‖ ^ n * ‖f‖) := by gcongr; exact hb u
    _ = _ := by ring

theorem cont_coef (v : V) : Continuous fun u : V => (2 * π * I * (omJ J v u : ℂ)) :=
  continuous_const.mul (Complex.continuous_ofReal.comp (omL J v).continuous)

theorem norm_coef (v u : V) : ‖(2 * π * I * (omJ J v u : ℂ))‖ ≤ (2 * π * ‖v‖) * ‖u‖ := by
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_ofNat]
  rw [mul_assoc (2 * π)]
  have := abs_omJ_le (J := J) v u
  gcongr

theorem integrable_dH (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) :
    Integrable fun u => gau u • dH ρ v (ρ u f) := by
  simp only [(calc' hJ h hf).2.2.2, smul_add]
  exact (h.integrable _).add (integrable_coef h f (cont_coef v) (2 * π * ‖v‖) 1 fun u => by
    rw [pow_one]; exact norm_coef v u)

theorem integrable_dH_dH (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (p q : V) :
    Integrable fun u => gau u • dH ρ p (dH ρ q (ρ u f)) := by
  have c1 := calc' hJ h hf
  have c2 := calc' hJ h (c1.1 q)
  have e : ∀ u, gau u • dH ρ p (dH ρ q (ρ u f)) = gau u • dH ρ p (ρ u (dH ρ q f)) +
      (gau u • (2 * π * I * (omJ J q u : ℂ)) • ρ u (dH ρ p f) +
        gau u • ((2 * π * I * (omJ J q u : ℂ)) * (2 * π * I * (omJ J p u : ℂ))) • ρ u f) := by
    intro u
    rw [c1.2.2.2 q, dH_add _ (c2.2.1 u) (Osc.sm_smul _ (c1.2.1 u)), dH_smul _ _ (c1.2.1 u), c1.2.2.2 p,
      smul_add, smul_add, smul_add, smul_smul _ _ (ρ u f)]
  simp only [e]
  refine (integrable_dH hJ h (c1.1 q) p).add ((integrable_coef h _ (cont_coef q) (2 * π * ‖q‖) 1 fun u => by
    rw [pow_one]; exact norm_coef q u).add (integrable_coef h _ ((cont_coef q).mul (cont_coef p))
      ((2 * π * ‖q‖) * (2 * π * ‖p‖)) 2 fun u => ?_))
  rw [norm_mul]
  calc _ ≤ ((2 * π * ‖q‖) * ‖u‖) * ((2 * π * ‖p‖) * ‖u‖) :=
        mul_le_mul (norm_coef q u) (norm_coef p u) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem integral_dH_dH (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (p q : V) :
    ∫ u, gau u • dH ρ p (dH ρ q (ρ u f)) = dH ρ p (dH ρ q (proj h f)) := by
  have c1 := calc' hJ h hf
  have sP : Sm ρ (proj h f) := (Osc.good_proj hJ h f).sm hJ
  have e1 : dH ρ q (proj h f) = ∫ u, gau u • dH ρ q (ρ u f) := by
    have := dH_integral V B (omL J) ρ (omL_self hJ) h V volume (fun u => gau u • ρ u f)
      (fun u => Osc.sm_smul _ (c1.2.1 u)) (h.integrable f) sP q
      (by simp only [dH_smul _ _ (c1.2.1 _)]; exact integrable_dH hJ h hf q)
    simpa only [dH_smul _ _ (c1.2.1 _), proj_apply] using this
  have s2 : ∀ u, Sm ρ (dH ρ q (ρ u f)) := fun u => (calc' hJ h (c1.2.1 u)).1 q
  have := dH_integral V B (omL J) ρ (omL_self hJ) h V volume (fun u => gau u • dH ρ q (ρ u f))
      (fun u => Osc.sm_smul _ (s2 u)) (integrable_dH hJ h hf q) (e1 ▸ (calc' hJ h sP).1 q) p
      (by simp only [dH_smul _ _ (s2 _)]; exact integrable_dH_dH hJ h hf p q)
  rw [e1, this]
  simp only [dH_smul _ _ (s2 _)]

theorem integral_quad (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f)
    {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) :
    (Integrable fun u => gau u • quad ρ c p q (ρ u f)) ∧
      ∫ u, gau u • quad ρ c p q (ρ u f) = quad ρ c p q (proj h f) := by
  have hi : ∀ i ∈ Finset.univ, Integrable fun u => c i • gau u • dH ρ (p i) (dH ρ (q i) (ρ u f)) :=
    fun i _ => (integrable_dH_dH hJ h hf (p i) (q i)).smul (c i)
  simp only [quad, Finset.smul_sum, smul_comm (gau _) (c _)]
  refine ⟨integrable_finset_sum _ hi, ?_⟩
  rw [integral_finset_sum _ hi]
  simp only [integral_smul, integral_dH_dH hJ h hf]

theorem moved_vacuum_deriv : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (a : ℝ → V →L[ℝ] V) (X : V →L[ℝ] V), a 0 = 1 → HasDerivAt a X 0 → (∀ t x y, omJ J (a t x) (a t y) = omJ J x y) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (omJ J) X c p q → (∃ C : ℝ, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x, ‖(∫ u, gau u • ρ (a t u) (proj h x)) - proj h x‖ ≤ C * |t| * ‖x‖) ∧ ∃ lam : ℂ, ∀ x, HasDerivAt (fun t : ℝ => ∫ u, gau u • ρ (a t u) (proj h x)) (quad ρ c p q (proj h x) + lam • proj h x) 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h a X a0 ha hom κ _ c p q hq
  obtain ⟨⟨C, hC⟩, -, hl⟩ := VacBd.vacuum_bound V B J ρ hJ h
  have sP : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨K, hK0, hK⟩ := ha.hasFDerivAt.isBigO_sub.exists_nonneg
  have hK := hK.bound
  simp only [a0, sub_zero, Real.norm_eq_abs] at hK
  set b : V → ℝ := fun u => |C| * K * (‖u‖ ^ 1 * ‖gau u‖) + π * K * ‖proj h‖ * (‖u‖ ^ 2 * ‖gau u‖) with hb
  have bi : Integrable b :=
    ((Osc.integrable_pow_gau 1).const_mul _).add ((Osc.integrable_pow_gau 2).const_mul _)
  have key : ∀ t, ‖a t - 1‖ ≤ K * |t| → ∀ x u,
      ‖gau u • ρ (a t u) (proj h x) - gau u • ρ u (proj h x)‖ ≤ b u * ‖x‖ * |t| := by
    intro t ht x u
    have hz : ‖a t u - u‖ ≤ K * |t| * ‖u‖ := by
      have := (a t - 1).le_opNorm u
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at this
      exact this.trans (by gcongr)
    have h1 := norm_sub_le hJ h (sP x) u (a t u - u)
    rw [add_sub_cancel] at h1
    have h2 : ‖dH ρ (a t u - u) (proj h x)‖ ≤ |C| * (K * |t| * ‖u‖) * ‖x‖ :=
      (hC _ _).trans (by gcongr; exact le_abs_self C)
    have h3 : π * (‖u‖ * ‖a t u - u‖) * ‖proj h x‖ ≤ π * (‖u‖ * (K * |t| * ‖u‖)) * (‖proj h‖ * ‖x‖) := by
      gcongr; exact (proj h).le_opNorm x
    rw [← smul_sub, norm_smul]
    calc _ ≤ ‖gau u‖ * (|C| * (K * |t| * ‖u‖) * ‖x‖ + π * (‖u‖ * (K * |t| * ‖u‖)) * (‖proj h‖ * ‖x‖)) := by
          gcongr; linarith
      _ = _ := by simp only [hb]; ring
  refine ⟨⟨∫ u, b u, ?_⟩, ?_⟩
  · filter_upwards [hK] with t ht x
    have i1 : Integrable fun u => gau u • ρ (a t u) (proj h x) := (h.twist (a t) (hom t)).integrable _
    have e : proj h x = ∫ u, gau u • ρ u (proj h x) := (Osc.proj_proj hJ h x).symm
    calc _ = ‖∫ u, (gau u • ρ (a t u) (proj h x) - gau u • ρ u (proj h x))‖ := by
          rw [integral_sub i1 (h.integrable _), ← e]
      _ ≤ ∫ u, b u * ‖x‖ * |t| :=
          norm_integral_le_of_norm_le ((bi.mul_const _).mul_const _) (Filter.Eventually.of_forall (key t ht x))
      _ = _ := by rw [integral_mul_const, integral_mul_const]; ring
  · choose l hl using hl
    refine ⟨-∑ i, c i * l (p i) (q i), fun x => ?_⟩
    have hG : ∀ u, fderiv ℝ (fun u => ρ u (proj h x)) u (X u) =
        quad ρ c p q (ρ u (proj h x)) - ρ u (quad ρ c p q (proj h x)) :=
      GlobalTheory.Mem.Lift.fderiv_eq_quad_comm V B (omL J) ρ (omL_self hJ) h X κ c p q hq _ (sP x)
    obtain ⟨i1, e1⟩ := integral_quad hJ h (sP x) c p q
    have i2 := h.integrable (quad ρ c p q (proj h x))
    have i3 : Integrable fun u => gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u) := by
      simp only [hG, smul_sub]; exact i1.sub i2
    have e3 : ∫ u, gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u) =
        quad ρ c p q (proj h x) + (-∑ i, c i * l (p i) (q i)) • proj h x := by
      simp only [hG, smul_sub]
      rw [integral_sub i1 i2, e1, Osc.proj_proj hJ, ← proj_apply h, neg_smul, sub_eq_add_neg, Finset.sum_smul]
      simp only [quad, map_sum, map_smul, hl, smul_smul]
    rw [← e3]
    have i4 : Integrable fun u =>
        ContinuousLinearMap.toSpanSingleton ℝ (gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u)) :=
      ((ContinuousLinearMap.smulRightL ℝ ℝ B 1).integrable_comp i3)
    have := (hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℝ) (μ := volume)
      (F := fun (t : ℝ) (u : V) => gau u • ρ (a t u) (proj h x)) (x₀ := 0)
      (F' := fun u => ContinuousLinearMap.toSpanSingleton ℝ (gau u • fderiv ℝ (fun u => ρ u (proj h x)) u (X u)))
      (bound := fun u => b u * ‖x‖) (s := {t | ‖a t - 1‖ ≤ K * |t|}) hK
      (fun t _ => ((h.twist (a t) (hom t)).integrable _).aestronglyMeasurable)
      ((h.twist (a 0) (hom 0)).integrable _) i4.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u t ht => by
        simpa only [a0, ContinuousLinearMap.one_apply, sub_zero, Real.norm_eq_abs] using key t ht x u)
      (bi.mul_const _) (Filter.Eventually.of_forall fun u => ?_)).2.hasDerivAt
    · rw [ContinuousLinearMap.integral_apply i4] at this
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using this
    · have h2 : HasDerivAt (fun t => a t u) (X u) 0 := by
        simpa using ha.clm_apply (hasDerivAt_const (0 : ℝ) u)
      have h3 := (ContDiff.differentiable (sP x) (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2
        (by simp [a0])
      exact (h3.const_smul (gau u)).hasFDerivAt

end GlobalTheory.Mem.Lift.MovedVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → MvPolynomial.eval (upt (ratPt S)) Q = 0) → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) → MvPolynomial.eval (upt Y) Q = 0 := by
  first | exact @GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | exact GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | (intros; apply GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_close_to_one_of_close_above_place : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (M : ℕ), ∃ M' : ℕ, ∀ z : K, (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → w.valuation K (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → v.valuation E (Algebra.norm E z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.NormCont.norm_close_to_one | exact GlobalTheory.NormCompat.NormCont.norm_close_to_one | (intros; apply GlobalTheory.NormCompat.NormCont.norm_close_to_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShiftStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite → (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) → Φ B *ᵥ v ∈ S := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | exact GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuationStatement
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_partial_zeta_continuation : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  first | exact @GlobalTheory.Mem.PartialZeta.partial_zeta_continuation | exact GlobalTheory.Mem.PartialZeta.partial_zeta_continuation | (intros; apply GlobalTheory.Mem.PartialZeta.partial_zeta_continuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictScalarsHomContinuousKrullStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_restrictScalarsHom' : ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω), Continuous (AlgEquiv.restrictScalarsHom E : G K Ω →* G E Ω) := by
  first | exact @GlobalTheory.restrictScalarsHom_continuous_krull | exact GlobalTheory.restrictScalarsHom_continuous_krull | (intros; apply GlobalTheory.restrictScalarsHom_continuous_krull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeightStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  first | exact @GlobalTheory.AlgWtHW.span_ratPt_orbit | exact GlobalTheory.AlgWtHW.span_ratPt_orbit | (intros; apply GlobalTheory.AlgWtHW.span_ratPt_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransvectionWeightVecExpansion
section
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.UnipotentWeights

noncomputable def tGL {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩

theorem diag_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * d i / d j) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    diagonal_mul, mul_diagonal, single_apply, one_apply]
  by_cases ha : i = a <;> by_cases hb : j = b
  · subst ha hb; simp [h]; field_simp [hd j]
  · by_cases hab : a = b <;> simp [ha, hb, hab]
  · subst hb; by_cases hab : a = j
    · subst hab; simp [h]
    · simp [ha, hab]
  · by_cases hab : a = b <;> simp [ha, hb, hab]

theorem poly_coeff_eq (K : ℕ) (x y : ℕ → ℂ) (hxy : ∀ s : ℂ, ∑ k ∈ Finset.range (K + 1), s ^ k * x k =
    ∑ k ∈ Finset.range (K + 1), s ^ k * y k) (k : ℕ) (hk : k ≤ K) : x k = y k := by
  let Q : Polynomial ℂ := ∑ k ∈ Finset.range (K + 1), Polynomial.C (x k - y k) * Polynomial.X ^ k
  have hQ : Q = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    have := hxy s
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hc := congrArg (fun p => Polynomial.coeff p k) hQ
  simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single k] at hc
  · simpa [sub_eq_zero] using hc
  · intro m _ hm; simp [Ne.symm hm]
  · intro hk'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'

end GlobalTheory.UnipotentWeights

namespace GlobalTheory.UnipotentWeights

theorem prod_single_zpow {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ l, d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l) = d i := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem prod_wt_shift {n : ℕ} (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (i j : Fin n) (μ : Fin n → ℤ) (k : ℕ) :
    ∏ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      (∏ l, d l ^ μ l) * (d i / d j) ^ k := by
  have hpt : ∀ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      d l ^ μ l * ((d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l)) ^ k *
        ((d l ^ ((Pi.single j (1 : ℤ) : Fin n → ℤ) l)) ^ k)⁻¹) := by
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [zpow_add₀ (hd l), mul_sub, zpow_sub₀ (hd l), div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm ((Pi.single i (1:ℤ) : Fin n → ℤ) l), mul_comm ((Pi.single j (1:ℤ) : Fin n → ℤ) l)]
  simp_rw [hpt]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow,
    Finset.prod_pow, prod_single_zpow, prod_single_zpow, div_pow, div_eq_mul_inv]

end GlobalTheory.UnipotentWeights

namespace GlobalTheory

open GlobalTheory.UnipotentWeights in

theorem transvection_weightVec_expansion :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∀ (μ : Fin n → ℤ) (v : ι → ℂ), IsWtVec Φ μ v →
        ∃ (K : ℕ) (w : ℕ → ι → ℂ), w 0 = v ∧
          (∀ k : ℕ, IsWtVec Φ (μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1)) (w k)) ∧
          ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
            Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
  intro n ι _ _ Φ hΦ i j hij μ v hv
  obtain ⟨P, hP⟩ := polyRep_transvection_entries_poly n ι Φ hΦ i j hij
  let K : ℕ := Finset.univ.sup (fun ab : ι × ι => (P ab.1 ab.2).natDegree)
  have hK : ∀ a b, (P a b).natDegree < K + 1 := fun a b =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun ab : ι × ι => (P ab.1 ab.2).natDegree) (Finset.mem_univ (a, b)))
  let w : ℕ → ι → ℂ := fun k a => ∑ b, (P a b).coeff k * v b
  have hexp : ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
      Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
    intro s B hB
    ext a
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]
    simp_rw [hP s B hB a, Polynomial.eval_eq_sum_range' (hK a _) s, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  refine ⟨K, w, ?_, ?_, hexp⟩
  · have h0 := hexp 0 1 (by simp)
    rw [hΦ.one, one_mulVec, Finset.sum_range_succ'] at h0
    simpa using h0.symm
  · intro k D hD
    by_cases hk : K < k
    · have hw : w k = 0 := by
        funext a
        simp only [w, Pi.zero_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hK a b) hk), zero_mul]
      rw [hw, mulVec_zero, smul_zero]
    push_neg at hk
    set d : Fin n → ℂ := fun l => D.val l l with hd_def
    have hDd : D.val = diagonal d := ((isDiag_iff_diagonal_diag _).1 hD).symm
    have hd : ∀ l, d l ≠ 0 := by
      have hdet : D.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
      rw [hDd, det_diagonal, Finset.prod_ne_zero_iff] at hdet
      exact fun l => hdet l (Finset.mem_univ l)
    set lam : ℂ := ∏ l, D.val l l ^ μ l with hlam
    have hcomm : ∀ s : ℂ, D * tGL hij s = tGL hij (s * d i / d j) * D := by
      intro s
      ext1
      simp only [Units.val_mul, tGL]
      rw [hDd]
      exact diag_mul_transvection hij d hd s
    have hmain : ∀ s : ℂ, Φ D *ᵥ (∑ k ∈ Finset.range (K + 1), s ^ k • w k) =
        lam • ∑ k ∈ Finset.range (K + 1), (s * d i / d j) ^ k • w k := by
      intro s
      rw [← hexp s (tGL hij s) rfl, ← hexp _ (tGL hij (s * d i / d j)) rfl, mulVec_mulVec, ← hΦ.mul, hcomm,
        hΦ.mul, ← mulVec_mulVec, hv D hD, mulVec_smul]
    have hcoord : ∀ a, (Φ D *ᵥ w k) a = (lam * (d i / d j) ^ k) * w k a := by
      intro a
      refine poly_coeff_eq K (fun m => (Φ D *ᵥ w m) a) (fun m => (lam * (d i / d j) ^ m) * w m a) ?_ k hk
      intro s
      have := congrFun (hmain s) a
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun m _ => by ring
    ext a
    rw [hcoord a, Pi.smul_apply, smul_eq_mul, prod_wt_shift d hd i j μ k]

end GlobalTheory
end


import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.LatticeTraceImaginaryPart
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexConjugate

namespace Pin2

theorem star_real_smul {g : ℕ} (t : ℝ) (v : Fin g → ℂ) : star ((t : ℂ) • v) = (t : ℂ) • star v := by
  ext i
  simp

theorem form_zero {g : ℕ} (D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (addL : ∀ z z' w, D (z + z') w = D z w + D z' w) (smulL : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (addR : ∀ z w w', D z (w + w') = D z w + D z w') (smulR : ∀ (t : ℝ) z w, D z ((t : ℂ) • w) = t * D z w)
    (h0 : ∀ p ∈ S, ∀ q ∈ S, (D (star p) (star q)).im = 0) (z w : Fin g → ℂ) : D z w = 0 := by
  have hrs : ∀ (t : ℝ) (u : Fin g → ℂ), t • u = (t : ℂ) • u := fun t u => by
    ext i
    simp [Complex.real_smul]
  have hstar_smul : ∀ (t : ℝ) (u : Fin g → ℂ), star (t • u) = t • star u := fun t u => by
    rw [hrs, hrs, star_real_smul]
  have hD0 : ∀ u, D 0 u = 0 := fun u => by simpa using smulL 0 0 u
  have hD0' : ∀ u, D u 0 = 0 := fun u => by simpa using smulR 0 u 0

  let N1 : Submodule ℝ (Fin g → ℂ) :=
    { carrier := {u | ∀ q ∈ S, (D (star u) (star q)).im = 0}
      add_mem' := by
        intro a b ha hb q hq
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [star_add, addL, Complex.add_im, ha q hq, hb q hq, add_zero]
      zero_mem' := by
        intro q _
        rw [star_zero, hD0, Complex.zero_im]
      smul_mem' := by
        intro t a ha q hq
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hstar_smul, hrs, smulL, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha q hq, mul_zero,
          zero_mul, add_zero] }
  have hN1 : ∀ u, u ∈ N1 := by
    intro u
    have h : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ N1 := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      intro p hp
      show ∀ q ∈ S, _
      exact h0 p hp
    exact h Submodule.mem_top
  have h1 : ∀ u, ∀ q ∈ S, (D u (star q)).im = 0 := by
    intro u
    have hm : ∀ q ∈ S, (D (star (star u)) (star q)).im = 0 := hN1 (star u)
    rw [star_star] at hm
    exact hm

  let N2 : Submodule ℝ (Fin g → ℂ) :=
    { carrier := {q | ∀ u, (D u (star q)).im = 0}
      add_mem' := by
        intro a b ha hb u
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [star_add, addR, Complex.add_im, ha u, hb u, add_zero]
      zero_mem' := by
        intro u
        rw [star_zero, hD0', Complex.zero_im]
      smul_mem' := by
        intro t a ha u
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hstar_smul, hrs, smulR, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha u, mul_zero,
          zero_mul, add_zero] }
  have hN2 : ∀ q, q ∈ N2 := by
    intro q
    have h : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ N2 := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      intro p hp
      show ∀ u, _
      exact fun u => h1 u p hp
    exact h Submodule.mem_top
  have h2 : ∀ u q, (D u q).im = 0 := by
    intro u q
    have hm : ∀ u, (D u (star (star q))).im = 0 := hN2 (star q)
    rw [star_star] at hm
    exact hm u
  have hre : (D z w).re = 0 := by
    have h := h2 (Complex.I • z) w
    rw [smulL, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h
    exact h
  exact Complex.ext_iff.2 ⟨by simp [hre], by simp [h2 z w]⟩

section Hf

variable {ι : Type} [Fintype ι]

theorem hf_add_left (v v' w : EuclideanSpace ℂ ι) : Hf (v + v') w = Hf v w + Hf v' w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_add_right (v w w' : EuclideanSpace ℂ ι) : Hf v (w + w') = Hf v w + Hf v w' := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_smul_left (t : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (t • v) w = t * Hf v w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_real_smul_right (t : ℝ) (v w : EuclideanSpace ℂ ι) : Hf v ((t : ℂ) • w) = t * Hf v w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_re_nonneg (v : EuclideanSpace ℂ ι) : 0 ≤ (Hf v v).re := by
  unfold Hf
  simp [inner_self_nonneg]
  exact Finset.sum_nonneg fun x _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

end Hf

section HermForm

variable {g : ℕ}

theorem hm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_real_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

end HermForm

end Pin2

section Pin2

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem lattice_trace_imaginary_part (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (a b : (W.F.Di (W.ik k)).La) :
    (Hf (Lmap hU hσ W A (star (W.Pm a))) (Lmap hU hσ W A (star (W.Pm b)))).im =
        A.sg * ((Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E)
          ((W.φ k b : (U.X k).Λ) : Fin r → E)) : ℚ) : ℝ) ∧
      (star (hermForm Wu.Hm (star (star (W.Pm a))) (star (star (W.Pm b))))).im =
        ((Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E)
          ((W.φ k b : (U.X k).Λ) : Fin r → E)) : ℚ) : ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [← pin1 hU hσ W A hx a, ← pin1 hU hσ W A hx b]
    exact A.im_eq _ (W.φ k a).2 _ (W.φ k b).2
  · rw [star_star, star_star, Complex.star_def, Complex.conj_im, Wu.c1]
    have hi := W.isom k a b
    rw [neg_mul, map_neg] at hi
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hi
    push_cast at hr
    linarith

theorem pin2 (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (z z' : Fin W.g → ℂ) :
    Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') = star (hermForm Wu.Hm (star z) (star z')) := by
  have key : ∀ z z', Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') -
      (A.sg : ℂ) * star (hermForm Wu.Hm (star z) (star z')) = 0 := by
    intro z z'
    refine Pin2.form_zero (fun z z' => Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') -
        (A.sg : ℂ) * star (hermForm Wu.Hm (star z) (star z')))
      (Set.range W.Pm) W.per.2.2.2.1 ?_ ?_ ?_ ?_ ?_ z z'
    · intro z z' w
      simp only [map_add, Pin2.hf_add_left, star_add, Pin2.hm_add_left]
      ring
    · intro t z w
      simp only [map_smul, Pin2.hf_smul_left, star_smul, Pin2.hm_smul_left, star_mul', star_star]
      ring
    · intro z w w'
      simp only [map_add, Pin2.hf_add_right, star_add, Pin2.hm_add_right]
      ring
    · intro t z w
      simp only [map_smul, Pin2.hf_real_smul_right, Pin2.star_real_smul, Pin2.hm_real_smul_right, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      ring
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      obtain ⟨h1, h2⟩ := lattice_trace_imaginary_part hU hσ W A hx Wu a b
      show (Hf (Lmap hU hσ W A (star (W.Pm a))) (Lmap hU hσ W A (star (W.Pm b))) -
        (A.sg : ℂ) * star (hermForm Wu.Hm (star (star (W.Pm a))) (star (star (W.Pm b))))).im = 0
      rw [Complex.sub_im, Complex.im_ofReal_mul, h1, h2]
      ring
  rcases A.sg_pm with h | h
  · have := key z z'
    rw [h, Complex.ofReal_one, _root_.one_mul, sub_eq_zero] at this
    exact this
  · rcases Nat.eq_zero_or_pos W.g with hg | hg
    · have hz : ∀ v : Fin W.g → ℂ, v = 0 := fun v => funext fun i => absurd i.2 (by omega)
      rw [hz z, hz z', map_zero]
      simp [Hf, hermForm]
    · exfalso
      obtain ⟨v, hv⟩ : ∃ v : Fin W.g → ℂ, v = Pi.single (⟨0, hg⟩ : Fin W.g) 1 := ⟨_, rfl⟩
      have hv0 : star v ≠ 0 := by
        intro h0
        have := congrFun h0 ⟨0, hg⟩
        simp [hv] at this
      have hpos := Wu.pos (star v) hv0
      have hk := key v v
      rw [h, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_neg_eq_add] at hk
      have hre := congrArg Complex.re hk
      rw [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hre
      linarith [Pin2.hf_re_nonneg (Lmap hU hσ W A v)]

end Pin2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable {r : ℕ}

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  have hsq : ∀ σ : D.host.E →+* ℂ, σ D.host.xi0 ^ 2 =
      1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ^ 2 * (-(D.host.d : ℂ))) := by
    intro σ
    have e : D.host.xi0 ^ 2 =
        1 / (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ^ 2 * (-(D.host.d : D.host.E))) := by
      simp only [Formalism.BasicNotions.Host.xi0]
      rw [div_pow, mul_pow, D.host.sqrtMinusD_sq]
      ring
    rw [← map_pow, e]
    simp
  have e2 : ‖τ D.host.xi0‖ ^ 2 = ‖D.host.φ₀ D.host.xi0‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow, hsq τ, hsq D.host.φ₀]
  have ha := norm_nonneg (τ D.host.xi0)
  have hb := norm_nonneg (D.host.φ₀ D.host.xi0)
  show ‖τ D.host.xi0‖ = ‖D.host.φ₀ D.host.xi0‖
  exact le_antisymm (by nlinarith) (by nlinarith)

theorem xi_eq (hP : FactPrincipalDatum) (D : D7) (X : Data D.host.E r)
    (hX : ∀ τ : D.host.E →+* ℂ, ‖τ X.ξ0‖ = xiR D) : X.ξ0 = D.host.xi0 ∨ X.ξ0 = -D.host.xi0 := by
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero hP D
  have hcξ : IsCMField.complexConj D.host.E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hcx : IsCMField.complexConj D.host.E D.host.xi0 = -D.host.xi0 := conj_xi0_alt D
  have hcu : IsCMField.complexConj D.host.E (X.ξ0 / D.host.xi0) = X.ξ0 / D.host.xi0 := by
    rw [map_div₀, hcξ, hcx, neg_div_neg_eq]
  have hτx : D.host.φ₀ D.host.xi0 ≠ 0 := (map_ne_zero D.host.φ₀).2 hx0
  have hn : ‖D.host.φ₀ (X.ξ0 / D.host.xi0)‖ = 1 := by
    have e : ‖D.host.φ₀ D.host.xi0‖ = xiR D := rfl
    rw [map_div₀, norm_div, hX D.host.φ₀, ← e, div_self (norm_ne_zero_iff.2 hτx)]
  have hreal : starRingEnd ℂ (D.host.φ₀ (X.ξ0 / D.host.xi0)) = D.host.φ₀ (X.ξ0 / D.host.xi0) := by
    rw [← IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀, hcu]
  have hsq : D.host.φ₀ (X.ξ0 / D.host.xi0) ^ 2 = 1 := by
    have h1 := Complex.conj_eq_iff_re.1 hreal
    rw [← h1] at hn ⊢
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    have h2 : (D.host.φ₀ (X.ξ0 / D.host.xi0)).re ^ 2 = 1 := by rw [← sq_abs, hn, one_pow]
    exact_mod_cast h2
  have hu2 : (X.ξ0 / D.host.xi0) ^ 2 = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, hsq, map_one]
  have hfac : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = 0 := by
    have e : (X.ξ0 / D.host.xi0 - 1) * (X.ξ0 / D.host.xi0 + 1) = (X.ξ0 / D.host.xi0) ^ 2 - 1 := by ring
    rw [e, hu2, sub_self]
  rcases mul_eq_zero.1 hfac with h | h
  · left
    exact (div_eq_one_iff_eq hx0).1 (sub_eq_zero.1 h)
  · right
    have h3 : X.ξ0 / D.host.xi0 = -1 := eq_neg_of_add_eq_zero_left h
    rw [div_eq_iff hx0] at h3
    rw [h3]
    ring

theorem herm_single (D : D7) (G : Matrix (Fin r) (Fin r) D.host.E) (w : Fin r → D.host.E) (i : Fin r) :
    herm G w (Pi.single i 1) = Matrix.vecMul w G i := by
  unfold herm
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [cc]
  · intro b _ hb
    simp [Pi.single_apply, hb, cc]
  · simp

theorem eq_zero_of_herm (D : D7) (X : Data D.host.E r) {w : Fin r → D.host.E}
    (hw : ∀ v ∈ X.Λ, herm X.Gm w v = 0) : w = 0 := by
  let T : Submodule D.host.E (Fin r → D.host.E) :=
    { carrier := {v | herm X.Gm w v = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : herm X.Gm w (a + b) = herm X.Gm w a + herm X.Gm w b := by
          simp only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]
        rw [e, ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, herm, Pi.zero_apply, cc, map_zero, mul_zero, Finset.sum_const_zero]
      smul_mem' := by
        intro c v hv
        simp only [Set.mem_setOf_eq] at hv ⊢
        have e : herm X.Gm w (c • v) = cc c * herm X.Gm w v := by
          simp only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
        rw [e, hv, mul_zero] }
  have hsp : Submodule.span D.host.E (X.Λ : Set (Fin r → D.host.E)) ≤ T :=
    Submodule.span_le.mpr fun v hv => hw v hv
  rw [X.Λ_span] at hsp
  have hvm : Matrix.vecMul w X.Gm = 0 := by
    funext i
    have h1 : Pi.single i 1 ∈ T := hsp Submodule.mem_top
    rw [← herm_single D X.Gm w i]
    exact h1
  exact Matrix.eq_zero_of_vecMul_eq_zero X.Gm_det hvm

theorem lat_dual (hP : FactPrincipalDatum) {D : D7} (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) (y : Fin D.R.r → D.host.E) :
    y ∈ ((T.U j σ).X k).Λ ↔
      ∀ z ∈ ((T.U j σ).X k).Λ, D.host.xi0 * herm ((T.U j σ).X k).Gm y z ∈ Dinv D := by
  obtain ⟨-, -, -, -, -, gg, ee, F, ik, φ, hiso, -⟩ := h.unf j hj σ hσ
  have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  obtain ⟨ε, hε, htr⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ ∀ u : D.host.E,
      Algebra.trace ℚ D.host.E (D.host.xi0 * u) =
        (ε : ℚ) * Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * u) := by
    rcases xi_eq hP D ((T.U j σ).X k) (h.xiAbs j hj σ hσ k) with hξ | hξ
    · refine ⟨-1, by norm_num, fun u => ?_⟩
      rw [hξ, neg_mul, map_neg]
      push_cast
      ring
    · refine ⟨1, by norm_num, fun u => ?_⟩
      rw [hξ, neg_neg]
      push_cast
      ring
  have htr' : ∀ u : D.host.E, Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * u) =
      (ε : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * u) := by
    intro u
    rw [htr u, ← mul_assoc]
    have : ((ε : ℚ) * ε) = 1 := by exact_mod_cast hε
    rw [this, one_mul]
  constructor
  · intro hy z hz
    rw [mem_dual h1ne]
    intro a ha
    obtain ⟨c, rfl⟩ := (mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E c) • y ∈ ((T.U j σ).X k).Λ := by
      rw [algebraMap_smul]; exact Submodule.smul_mem _ c hy
    have e : D.host.xi0 * herm ((T.U j σ).X k).Gm y z * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * herm ((T.U j σ).X k).Gm ((algebraMap (𝓞 D.host.E) D.host.E c) • y) z := by
      rw [herm_smul_left]; ring
    rw [e, htr]
    have hE := hiso k ((φ k).symm ⟨_, hy'⟩) ((φ k).symm ⟨z, hz⟩)
    simp only [LinearEquiv.apply_symm_apply] at hE
    refine ⟨ε * (F.Di (ik k)).EF ((φ k).symm ⟨_, hy'⟩) ((φ k).symm ⟨z, hz⟩), ?_⟩
    rw [eq_intCast, Int.cast_mul, hE]
  · intro hy
    have hint : ∀ a : (F.Di (ik k)).La, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ D.host.E
        (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E)) := by
      intro a
      have h2 := (mem_dual h1ne).1 (hy _ (φ k a).2) 1 (one_mem_one _)
      rw [Algebra.traceForm_apply, mul_one] at h2
      obtain ⟨n, hn⟩ := h2
      refine ⟨ε * n, ?_⟩
      rw [htr', ← hn, eq_intCast, Int.cast_mul]
    let ψ : (F.Di (ik k)).La →+ ℤ := AddMonoidHom.mk' (fun a => Classical.choose (hint a)) (fun a b => by
      apply Int.cast_injective (α := ℚ)
      have e1 := Classical.choose_spec (hint (a + b))
      have e2 := Classical.choose_spec (hint a)
      have e3 := Classical.choose_spec (hint b)
      rw [Int.cast_add, e1, e2, e3, map_add, Submodule.coe_add, herm_add_right, mul_add, map_add])
    obtain ⟨b, hb⟩ := (F.Di (ik k)).unimod.2 ψ.toIntLinearMap
    set w := y - (φ k b : Fin D.R.r → D.host.E) with hw
    have hzero : ∀ a : (F.Di (ik k)).La,
        Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 *
          herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E)) = 0 := by
      intro a
      have e1 : herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E) =
          herm ((T.U j σ).X k).Gm w (φ k a) + herm ((T.U j σ).X k).Gm (φ k b) (φ k a) := by
        rw [← herm_add_left, hw, sub_add_cancel]
      have e2 : (((F.Di (ik k)).EF b a : ℤ) : ℚ) = (ψ a : ℚ) := by
        rw [hb]; rfl
      rw [hiso k b a] at e2
      have e3 : (ψ a : ℚ) = Algebra.trace ℚ D.host.E
          (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm y (φ k a : Fin D.R.r → D.host.E)) :=
        Classical.choose_spec (hint a)
      rw [e1, mul_add, map_add, ← e2] at e3
      linarith
    have hperp : ∀ a : (F.Di (ik k)).La, herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E) = 0 := by
      intro a
      have hsep : -((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm w (φ k a : Fin D.R.r → D.host.E) = 0 := by
        apply trace_sep D
        intro c
        let c' : 𝓞 D.host.E := ⟨cc (algebraMap (𝓞 D.host.E) D.host.E c),
          int_cc D (NumberField.RingOfIntegers.isIntegral_coe c)⟩
        have e4 := hzero (c' • a)
        rw [LinearEquiv.map_smul, Submodule.coe_smul, ← algebraMap_smul D.host.E c', herm_smul_right] at e4
        have e5 : cc (algebraMap (𝓞 D.host.E) D.host.E c') = algebraMap (𝓞 D.host.E) D.host.E c :=
          cc_cc D _
        rw [e5] at e4
        rw [← e4]
        congr 1
        ring
      rcases mul_eq_zero.1 hsep with h3 | h3
      · exact absurd (neg_eq_zero.1 h3) ((T.U j σ).X k).ξ0_ne
      · exact h3
    have hw0 : w = 0 := by
      apply eq_zero_of_herm D ((T.U j σ).X k)
      intro v hv
      have := hperp ((φ k).symm ⟨v, hv⟩)
      simpa using this
    have : y = (φ k b : Fin D.R.r → D.host.E) := by
      rw [← sub_eq_zero]; exact hw0
    rw [this]
    exact (φ k b).2

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB
end
end


import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Polynomial

namespace GlobalTheory.UnitaryCongruenceDet

noncomputable section

def ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_eq (x : E) : cc x = ccHom E x := rfl

theorem transpose_mul_mul_map {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γᵀ * G * γ.map (ccHom E) = G := by
  ext i j
  have hs : ∀ k, γ *ᵥ Pi.single k 1 = fun a => γ a k := by
    intro k; funext a; simp [mulVec, dotProduct, Pi.single_apply]
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [herm, cc_eq, hs] at hij
  simp only [mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, hij]
  simp [Pi.single_apply]

theorem det_mul_cc_det {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γ.det * cc γ.det = 1 := by
  have e := congrArg Matrix.det (transpose_mul_mul_map G γ h)
  have hd : (γ.map (ccHom E)).det = ccHom E γ.det := by rw [RingHom.map_det]; rfl
  rw [det_mul, det_mul, det_transpose, hd] at e
  rw [cc_eq]
  apply mul_right_cancel₀ hG
  linear_combination e

theorem isIntegral_of_left_eigen {r : ℕ} {Ω : Type} [Field Ω] [Algebra E Ω]
    (C : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hC : ∀ x ∈ Λ, C *ᵥ x ∈ Λ)
    (μ : Ω) (u : Fin r → Ω) (hu : u ≠ 0) (hμ : u ᵥ* C.map (algebraMap E Ω) = μ • u) :
    IsIntegral ℤ μ := by
  classical
  let φ := algebraMap E Ω
  let g : (Fin r → E) →ₗ[E] Ω :=
    { toFun := fun x => u ⬝ᵥ (fun a => φ (x a))
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add]
        rw [← dotProduct_add]; rfl
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, dotProduct,
          Algebra.smul_def]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  let N : Submodule ℤ Ω := (Λ.restrictScalars ℤ).map (g.restrictScalars ℤ)
  have hNfg : N.FG := (Submodule.FG.restrictScalars (R := ℤ) hfg).map _
  have hN : N ≠ ⊥ := by
    intro hN
    apply hu
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      intro x hx
      have : g x ∈ N := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      rw [hN, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker] at this
    simpa [g, φ, dotProduct, Pi.single_apply, apply_ite] using this
  refine isIntegral_of_smul_mem_submodule N hN hNfg μ ?_
  rintro n hn
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨C *ᵥ x, hC x hx, ?_⟩
  change u ⬝ᵥ (fun a => φ ((C *ᵥ x) a)) = μ • (u ⬝ᵥ fun a => φ (x a))
  have h1 : (fun a => φ ((C *ᵥ x) a)) = C.map φ *ᵥ (fun a => φ (x a)) := by
    funext a; exact RingHom.map_mulVec φ C x a
  rw [h1, dotProduct_mulVec, hμ, smul_dotProduct, smul_eq_mul]

theorem prod_eq_one_add {Ω : Type} [Field Ω] (M : ℕ) (hM : (M : Ω) ≠ 0) (s : Multiset Ω)
    (hs : ∀ l ∈ s, IsIntegral ℤ ((l - 1) / (M : Ω))) :
    ∃ z : Ω, IsIntegral ℤ z ∧ s.prod = 1 + M * z := by
  have hMint : IsIntegral ℤ (M : Ω) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Ω (M : ℤ)))
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz, hprod⟩ := ih (fun l hl => hs l (Multiset.mem_cons_of_mem hl))
    have ha := hs a (Multiset.mem_cons_self a s)
    set w := (a - 1) / (M : Ω) with hw
    have ha' : a = 1 + M * w := by rw [hw]; field_simp; ring
    refine ⟨w + z + M * w * z, (ha.add hz).add ((hMint.mul ha).mul hz), ?_⟩
    rw [Multiset.prod_cons, hprod, ha']
    ring

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r),
    3 ≤ M →
    (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) →
    ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M X hM hΓ γ hγ
  classical
  obtain ⟨⟨hherm, -⟩, hcong⟩ := (hΓ γ).1 hγ
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ X.Λ, A *ᵥ x ∈ X.Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots, IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply isIntegral_of_left_eigen A X.Λ X.Λ_fg X.Λ_span hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _
  have hint : IsIntegral ℤ ((g.det - 1) / (M : E)) := by
    have h1 : φ ((g.det - 1) / (M : E)) = z := by
      rw [map_div₀, map_sub, map_one, map_natCast, hφdet]; field_simp; ring
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 (by change IsIntegral ℤ (φ _); rw [h1]; exact hz)
  have hc := det_mul_cc_det X.Gm g X.Gm_det hherm
  by_contra hne
  have hx : (⟨(g.det - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (g.det - 1) / (M : E) = 0 := congrArg Subtype.val h
    rcases div_eq_zero_iff.1 this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hME h
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((g.det - 1) / M)‖ := hσ
  have h1 : ‖σ g.det‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ g.det)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ g.det - 1‖ ≤ 2 := by
    have := norm_sub_le (σ g.det) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

end

end GlobalTheory.UnitaryCongruenceDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivFractionsBilinearFormula
section
set_option autoImplicit false

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine.UnitaryInv

theorem det_smul_one (z : ℂ) : (z • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq z := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply, ContinuousLinearMap.det]
  congr 1

theorem ae_affine_ne (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) : ∀ᵐ x : ℂ, a + b * x ≠ 0 := by
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  simp only [ne_eq, not_not, Set.mem_setOf_eq] at hx hy
  by_cases hb : b = 0
  · rcases h with h | h
    · simp [hb, h] at hx
    · exact absurd hb h
  · apply mul_left_cancel₀ hb
    linear_combination hx - hy

theorem integral_moebius (a b c d : ℂ) (hD : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ y : ℂ, G y = ∫ x : ℂ, (Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2)) •
      G ((c + d * x) / (a + b * x)) := by
  set s : Set ℂ := {x | a + b * x ≠ 0} with hs
  have hso : IsOpen s := isOpen_ne_fun (by fun_prop) continuous_const
  have hder : ∀ x ∈ s, HasFDerivWithinAt (fun x : ℂ => (c + d * x) / (a + b * x))
      (((a * d - b * c) / (a + b * x) ^ 2) • (1 : ℂ →L[ℝ] ℂ)) s x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℂ => c + d * x) d x := by
      simpa using ((hasDerivAt_id x).const_mul d).const_add c
    have h2 : HasDerivAt (fun x : ℂ => a + b * x) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).const_add a
    have h3 := h1.div h2 hx
    have h4 : HasDerivAt (fun x : ℂ => (c + d * x) / (a + b * x)) ((a * d - b * c) / (a + b * x) ^ 2) x := by
      have e : (a * d - b * c) / (a + b * x) ^ 2
          = (d * (a + b * x) - (c + d * x) * b) / (a + b * x) ^ 2 := by ring
      rw [e]
      exact h3
    exact h4.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : Set.InjOn (fun x : ℂ => (c + d * x) / (a + b * x)) s := by
    intro x hx y hy hxy
    have hx' : a + b * x ≠ 0 := hx
    have hy' : a + b * y ≠ 0 := hy
    simp only at hxy
    rw [div_eq_div_iff hx' hy'] at hxy
    apply mul_left_cancel₀ hD
    linear_combination hxy
  have key := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℂ) hso.measurableSet hder hinj G
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hD
  have hdb : d ≠ 0 ∨ -b ≠ 0 := by
    by_contra h
    push_neg at h
    have hb : b = 0 := by simpa using h.2
    simp [h.1, hb] at hD
  have him : ∀ᵐ y : ℂ, y ∈ (fun x : ℂ => (c + d * x) / (a + b * x)) '' s := by
    filter_upwards [ae_affine_ne d (-b) hdb] with y hy
    have e1 : a + b * ((a * y - c) / (d + -b * y)) = (a * d - b * c) / (d + -b * y) := by
      rw [eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e2 : c + d * ((a * y - c) / (d + -b * y)) = y * ((a * d - b * c) / (d + -b * y)) := by
      rw [← mul_div_assoc y, eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e3 : (a * d - b * c) / (d + -b * y) ≠ 0 := div_ne_zero hD hy
    refine ⟨(a * y - c) / (d + -b * y), ?_, ?_⟩
    · show a + b * ((a * y - c) / (d + -b * y)) ≠ 0
      rw [e1]; exact e3
    · show (c + d * ((a * y - c) / (d + -b * y))) / (a + b * ((a * y - c) / (d + -b * y))) = y
      rw [e1, e2, mul_div_assoc, div_self e3, mul_one]
  have hs' : ∀ᵐ x : ℂ, x ∈ s := ae_affine_ne a b hab
  rw [Measure.restrict_eq_self_of_ae_mem him, Measure.restrict_eq_self_of_ae_mem hs'] at key
  rw [key]
  congr 1
  ext x
  rw [det_smul_one, abs_of_nonneg (Complex.normSq_nonneg _)]

theorem qMat_eq (H : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    qMat H x = (H 0 0 + H 0 1 * x + H 1 0 * starRingEnd ℂ x + H 1 1 * (x * starRingEnd ℂ x)) /
      (1 + x * starRingEnd ℂ x) := by
  have : ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) = 1 + x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp only [qMat, qCoef, entries, lineVec, Fintype.sum_prod_type, Fin.sum_univ_two, this, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
  ring

theorem fsDens_eq (x : ℂ) :
    (fsDens x : ℂ) = 1 / (Real.pi * (1 + x * starRingEnd ℂ x) ^ 2) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, fsDens]; push_cast; ring

theorem one_add_ne (x : ℂ) : 1 + x * starRingEnd ℂ x ≠ 0 := by
  rw [Complex.mul_conj]
  have := Complex.normSq_nonneg x
  exact_mod_cast (by linarith : (1 + Complex.normSq x) ≠ 0)

theorem div_fractions_bilinear_formula (h0 h1 h2 h3 A B C D N : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hN : N ≠ 0) :
    (h0 + h1 * (C / A) + h2 * (D / B) + h3 * (C / A * (D / B))) / (N / (A * B))
      = (h0 * (A * B) + h1 * (C * B) + h2 * (D * A) + h3 * (C * D)) / N := by
  field_simp

theorem integral_qMat_unitary_conj (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    ∫ x : ℂ, qMat (U * H * star U) x ^ k * (fsDens x : ℂ) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have e := fun i j => congrFun (congrFun h1 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply, RCLike.star_def,
    if_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false] at e00 e01 e10 e11
  set p := U 0 0 with hp
  set q := U 0 1 with hq
  set r := U 1 0 with hr
  set t := U 1 1 with ht
  set a := starRingEnd ℂ p with ha
  set c := starRingEnd ℂ q with hc
  set b := starRingEnd ℂ r with hb
  set d := starRingEnd ℂ t with hd
  have hDD : (a * d - b * c) * (p * t - r * q) = 1 := by
    linear_combination (r * b + t * d) * e00 + e11 - (r * a + t * c) * e01 - 0 * e10
  have hD : a * d - b * c ≠ 0 := left_ne_zero_of_mul_eq_one hDD
  rw [integral_moebius a b c d hD (fun x => qMat H x ^ k * (fsDens x : ℂ))]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hD
  apply integral_congr_ae
  filter_upwards [ae_affine_ne a b hab] with x hx
  set y := starRingEnd ℂ x with hy
  have hcj : starRingEnd ℂ (a + b * x) = p + r * y := by simp [ha, hb, hy]
  have hcj2 : starRingEnd ℂ (c + d * x) = q + t * y := by simp [hc, hd, hy]
  have hcj3 : starRingEnd ℂ (a * d - b * c) = p * t - r * q := by simp [ha, hb, hc, hd]
  have hx' : p + r * y ≠ 0 := by rw [← hcj]; simpa only [ne_eq, map_eq_zero] using hx
  have hN : 1 + x * y ≠ 0 := one_add_ne x
  have hsum : (a + b * x) * (p + r * y) + (c + d * x) * (q + t * y) = 1 + x * y := by
    linear_combination e00 + x * e01 + y * e10 + x * y * e11
  have hm : 1 + (c + d * x) / (a + b * x) * ((q + t * y) / (p + r * y))
      = (1 + x * y) / ((a + b * x) * (p + r * y)) := by
    rw [← hsum, add_div ((a + b * x) * (p + r * y)), div_self (mul_ne_zero hx hx'), div_mul_div_comm]
  have hq' : qMat H ((c + d * x) / (a + b * x)) = qMat (U * H * star U) x := by
    rw [qMat_eq, qMat_eq, map_div₀, hcj, hcj2, hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, RCLike.star_def]
    rw [← hy, ← hp, ← hq, ← hr, ← ht, ← ha, ← hb, ← hc, ← hd]
    rw [div_fractions_bilinear_formula _ _ _ _ _ _ _ _ _ hx hx' hN]
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf : ((Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2) : ℝ) : ℂ) *
      (fsDens ((c + d * x) / (a + b * x)) : ℂ) = fsDens x := by
    rw [fsDens_eq, fsDens_eq, ← Complex.mul_conj, map_div₀, map_div₀, map_pow, hcj, hcj2, hcj3, hm, ← hy,
      div_mul_div_comm, hDD]
    generalize a + b * x = A at *
    generalize p + r * y = B at *
    generalize 1 + x * y = N at *
    field_simp
  simp only [Complex.real_smul]
  rw [hq', ← hf]
  ring

end GlobalTheory.FibLine.UnitaryInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLatticeStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionAlgebra_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι → Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.divAlg_order_no_small_lattice | exact GlobalTheory.divAlg_order_no_small_lattice | (intros; apply GlobalTheory.divAlg_order_no_small_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetCardDivCardInfCommutativeSubgroupStatement
section
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_card_div_card_inf_commutative_subgroup : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  first | exact @GlobalTheory.DCIndex.index_identity | exact GlobalTheory.DCIndex.index_identity | (intros; apply GlobalTheory.DCIndex.index_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConstStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_relIndex_inf_conj_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  first | exact @GlobalTheory.doubleCoset_relIndex_const | exact GlobalTheory.doubleCoset_relIndex_const | (intros; apply GlobalTheory.doubleCoset_relIndex_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjectiveStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_semidirect_rep_surjective : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N, DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X) = d := by
  first | exact @GlobalTheory.doubleCoset_semidirect_surj | exact GlobalTheory.doubleCoset_semidirect_surj | (intros; apply GlobalTheory.doubleCoset_semidirect_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomainStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_sum_fundamental_domain : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  first | exact @GlobalTheory.doubleCosetSum_adjoint | exact GlobalTheory.doubleCosetSum_adjoint | (intros; apply GlobalTheory.doubleCosetSum_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAwayStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_extend_away : ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S'] (d : S →+* DualNumber S), (∀ s, (d s).fst = s) → ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧ ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  first | exact @GlobalTheory.dualNumber_deformation_extends_away | exact GlobalTheory.dualNumber_deformation_extends_away | (intros; apply GlobalTheory.dualNumber_deformation_extends_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrExistsUnitPowEqMulUniformizerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_exists_unit_pow_eq_mul_uniformizer : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  first | (exact @GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif) | (exact GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif) | (intros; apply GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrimeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_of_principal_prime_localization : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  first | exact @GlobalTheory.dvr_loc_principal_prime | exact GlobalTheory.dvr_loc_principal_prime | (intros; apply GlobalTheory.dvr_loc_principal_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrSubringEqTopStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subring_eq_univ_of_uniformizer_generates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by
  first | exact @GlobalTheory.dvrSubring_eq_top | exact GlobalTheory.dvrSubring_eq_top | (intros; apply GlobalTheory.dvrSubring_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximalStatement
section
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_idempotents_of_comaximal : ∀ {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
  (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∃ e : Fin a → Module.End C W,
    (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
    (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
    (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  first | exact @GlobalTheory.eigenIdempotents_of_comaximal | exact GlobalTheory.eigenIdempotents_of_comaximal | (intros; apply GlobalTheory.eigenIdempotents_of_comaximal <;> assumption)
end


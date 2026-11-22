import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetConjUnitary
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol

def I0 : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹)

theorem I0_lt_top : I0 < ⊤ := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun z => ?_
  congr 1
  rw [Real.rpow_neg (by positivity), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]

def wt (l : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹ * ((1 + |l| * ‖z‖) ^ 3)⁻¹)

theorem measurable_wt (l : ℝ) : Measurable (wt l) := by
  unfold wt
  fun_prop

theorem lint_scale {l : ℝ} (hl : l ≠ 0) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) = ENNReal.ofReal ((l ^ 2)⁻¹) * I0 := by
  have hr : |l| ≠ 0 := abs_ne_zero.mpr hl
  have hm := Measure.map_addHaar_smul (volume : Measure ℂ) hr
  have hF : Measurable fun w : ℂ => ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) := by fun_prop
  have h1 : ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹)
      = ∫⁻ w : ℂ, ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) ∂(Measure.map (fun x : ℂ => |l| • x) volume) := by
    rw [lintegral_map hF (measurable_const_smul _)]
    refine lintegral_congr fun z => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_abs]
  rw [h1, hm, lintegral_smul_measure, Complex.finrank_real_complex]
  simp only [smul_eq_mul, I0]
  congr 2
  rw [abs_of_nonneg (by positivity), sq_abs]

theorem one_var (l : ℝ) :
    ∫⁻ z : ℂ, wt l z ≤ ENNReal.ofReal (2 * I0.toReal * (1 + l ^ 2)⁻¹) := by
  have hI : ENNReal.ofReal I0.toReal = I0 := ENNReal.ofReal_toReal I0_lt_top.ne
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rcases le_or_gt |l| 1 with h | h
  · have h1 : ∫⁻ z : ℂ, wt l z ≤ I0 := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + |l| * ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by nlinarith [norm_nonneg z, abs_nonneg l]))
      nlinarith
    refine h1.trans ?_
    conv_lhs => rw [← hI]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : l ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg l]
    have h3 : (1 : ℝ) ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · have hl : l ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    have h1 : ∫⁻ z : ℂ, wt l z ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + |l| * ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by linarith [norm_nonneg z]))
      nlinarith
    refine h1.trans ?_
    rw [lint_scale hl]
    conv_lhs => rw [← hI]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 1 ≤ l ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h3 : (l ^ 2)⁻¹ ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    nlinarith

theorem pi_bound {n : ℕ} (l : Fin n → ℝ) :
    ∫⁻ z : Fin n → ℂ, ∏ i, wt (l i) (z i) ≤
      ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod
    (f := fun i => wt (l i)) fun i => (measurable_wt (l i)).aemeasurable]
  refine (Finset.prod_le_prod' fun i _ => one_var (l i)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib]

theorem prod_le_pow {n K : ℕ} (hK : 3 * n ≤ K) {x : Fin n → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ a) (ha : 0 ≤ a) :
    ((1 + a) ^ K)⁻¹ ≤ ∏ i, ((1 + x i) ^ 3)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by have := h0 i; positivity) ?_
  calc ∏ i, (1 + x i) ^ 3 ≤ ∏ _i : Fin n, (1 + a) ^ 3 :=
        Finset.prod_le_prod (fun i _ => by have := h0 i; positivity)
          fun i _ => pow_le_pow_left₀ (by have := h0 i; positivity) (by linarith [hx i]) 3
    _ = (1 + a) ^ (3 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ (1 + a) ^ K := pow_le_pow_right₀ (by linarith) hK

theorem weight_le {n K : ℕ} (hK : 3 * n ≤ K) (l : Fin n → ℝ) {a d : ℝ} (z : Fin n → ℂ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (h1 : ∀ i, ‖z i‖ ≤ a) (h2 : ∀ i, |l i| * ‖z i‖ ≤ d) :
    ENNReal.ofReal (((1 + a) ^ K)⁻¹ * ((1 + d) ^ K)⁻¹) ≤ ∏ i, wt (l i) (z i) := by
  unfold wt
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul (prod_le_pow hK (fun i => norm_nonneg _) h1 ha)
    (prod_le_pow hK (fun i => by positivity) h2 hd) (by positivity)
    (Finset.prod_nonneg fun i _ => by positivity)

theorem det_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    det ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) = det X := by
  rw [det_mul, det_mul, mul_comm (det (U : Matrix (Fin n) (Fin n) ℂ)), mul_assoc, ← det_mul,
    mem_unitaryGroup_iff.mp U.2, det_one, mul_one]

theorem detW_eq {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    detW b = ∏ i, (1 + hb.eigenvalues i ^ 2) := by
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hb.eigenvalues) with hD
  have hs := hb.spectral_theorem
  have h1 : 1 + b * b = Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary (1 + D * D) := by
    rw [map_add, map_one, map_mul, ← hs]
  have h2 : 1 + D * D = diagonal fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    ext i
    simp [sq]
  rw [detW, h1, Unitary.conjStarAlgAut_apply, det_conj_unitary, h2, det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem repr_apply_lin {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hb.eigenvectorBasis.repr (Matrix.toEuclideanLin b y) i =
      (hb.eigenvalues i : ℂ) * hb.eigenvectorBasis.repr y i := by
  have hs : (Matrix.toEuclideanLin b).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hb
  have he : Matrix.toEuclideanLin b (hb.eigenvectorBasis i) =
      (hb.eigenvalues i : ℂ) • hb.eigenvectorBasis i := by
    have := hb.mulVec_eigenvectorBasis i
    apply PiLp.ext
    intro j
    have h2 := congrFun this j
    simpa [toLpLin_apply] using h2
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hs, he, inner_smul_left]
  simp

theorem map_isometry {n : ℕ} (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure]
    (R : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving R m m := by
  have hp := LinearIsometryEquiv.measurePreserving
    (⟨R.toLinearEquiv.restrictScalars ℝ, R.norm_map⟩ :
      EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
  have hc := Measure.isAddLeftInvariant_eq_smul m (volume : Measure (EuclideanSpace ℂ (Fin n)))
  refine ⟨R.continuous.measurable, ?_⟩
  have hm : Measure.map R (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := hp.map_eq
  conv_lhs => rw [hc]
  rw [Measure.map_smul, hm, ← hc]

theorem exists_scale (n : ℕ) (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure] :
    ∃ c : NNReal, ∀ P : (Fin n → ℂ) → ℝ≥0∞, Measurable P →
      ∫⁻ y, P (WithLp.ofLp y) ∂m = c * ∫⁻ x, P x := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  haveI : (Measure.map e m).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e m = c • (volume : Measure (Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun P hP => ?_⟩
  have h1 : ∫⁻ y, P (WithLp.ofLp y) ∂m = ∫⁻ x, P x ∂(Measure.map e m) := by
    rw [lintegral_map hP e.continuous.measurable]
    rfl
  rw [h1, hc, lintegral_smul_measure]
  rfl

theorem volume_bound : ∀ (n K : ℕ), 3 * n ≤ K → ∀ m : Measure (EuclideanSpace ℂ (Fin n)), m.IsAddHaarMeasure →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ∂m ≤
      ENNReal.ofReal (C * (detW b)⁻¹) := by
  intro n K hK m hm
  obtain ⟨c, hc⟩ := exists_scale n m
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  refine ⟨c * (2 * I0.toReal) ^ n, by positivity, fun b hb => ?_⟩
  set l := hb.eigenvalues with hl
  set R := hb.eigenvectorBasis.repr with hR
  let P : (Fin n → ℂ) → ℝ≥0∞ := fun x => ∏ i, wt (l i) (x i)
  have hP : Measurable P :=
    Finset.measurable_prod _ fun i _ => (measurable_wt (l i)).comp (measurable_pi_apply i)
  have hG : Measurable fun y : EuclideanSpace ℂ (Fin n) => P (WithLp.ofLp y) :=
    hP.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable
  have h1 : ∀ y : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ≤
        P (WithLp.ofLp (R y)) := by
    intro y
    refine weight_le hK l _ (norm_nonneg _) (norm_nonneg _) (fun i => ?_) (fun i => ?_)
    · rw [← R.norm_map y]
      exact PiLp.norm_apply_le (R y) i
    · rw [← R.norm_map (Matrix.toEuclideanLin b y)]
      refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le (R (Matrix.toEuclideanLin b y)) i)
      rw [hR, repr_apply_lin hb, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ∫⁻ y, P (WithLp.ofLp (R y)) ∂m := lintegral_mono h1
    _ = ∫⁻ y, P (WithLp.ofLp y) ∂m := (map_isometry m R).lintegral_comp hG
    _ = c * ∫⁻ x, P x := hc P hP
    _ ≤ c * ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
        gcongr
        exact pi_bound l
    _ = ENNReal.ofReal (c * (2 * I0.toReal) ^ n * (detW b)⁻¹) := by
        rw [detW_eq hb, mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ)) (by positivity),
          ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermOfCntEq
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Polarisation

noncomputable def cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (f j) 1

open Classical in
theorem cnt_apply {ι : Type} {m : ℕ} (f : Fin m → ι) (i : ι) :
    cnt f i = Fintype.card {j // f j = i} := by
  simp [cnt, Finsupp.finset_sum_apply, Finsupp.single_apply, Fintype.card_subtype]

theorem degree_cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : (cnt f).degree = m := by
  classical
  simp [cnt, map_sum]

theorem exists_perm_of_cnt_eq {ι : Type} {m : ℕ} {f g : Fin m → ι} (h : cnt f = cnt g) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  have hc : ∀ i, Nonempty ({j // g j = i} ≃ {j // f j = i}) := fun i => by
    refine Fintype.card_eq.1 ?_
    rw [← cnt_apply, ← cnt_apply, h]
  let e : ∀ i, {j // g j = i} ≃ {j // f j = i} := fun i => (hc i).some
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext j
  exact (Equiv.ofFiberEquiv_map e j).symm

theorem prod_X_eq {ι : Type} {m : ℕ} (f : Fin m → ι) (a : Fin m → ℝ) :
    ∏ j, (C (a j) * X (f j) : MvPolynomial ι ℝ) = monomial (cnt f) (∏ j, a j) := by
  classical
  have key : ∀ s : Finset (Fin m), ∏ j ∈ s, (C (a j) * X (f j) : MvPolynomial ι ℝ)
      = monomial (∑ j ∈ s, Finsupp.single (f j) 1) (∏ j ∈ s, a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, ih, X,
        C_mul_monomial, monomial_mul]
      simp
  exact key Finset.univ

theorem lin_pow {ι : Type} [Fintype ι] (n : ι → ℝ) (m : ℕ) :
    GlobalTheory.ArInt.lin n ^ m = ∑ f : Fin m → ι, monomial (cnt f) (∏ j, n (f j)) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset ι))
    (fun _ i => (C (n i) * X i : MvPolynomial ι ℝ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [GlobalTheory.ArInt.lin, h]
  exact Finset.sum_congr rfl fun f _ => prod_X_eq f (fun j => n (f j))

open Classical in

noncomputable def coef {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) : ℝ :=
  if h : ∃ f : Fin m → ι, cnt f = k then F h.choose else 0

theorem coef_cnt {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ)
    (hF : ∀ (f : Fin m → ι) (σ : Equiv.Perm (Fin m)), F (f ∘ σ) = F f) (f : Fin m → ι) :
    coef F (cnt f) = F f := by
  have h : ∃ g : Fin m → ι, cnt g = cnt f := ⟨f, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_cnt_eq h.choose_spec.symm
  rw [coef, dif_pos h, hσ, hF]

theorem coef_of_degree_ne {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) {k : ι →₀ ℕ}
    (hk : k.degree ≠ m) : coef F k = 0 := by
  refine dif_neg ?_
  rintro ⟨f, rfl⟩
  exact hk (degree_cnt f)

noncomputable def form {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials ι ℝ).constr ℝ (coef F)

theorem form_monomial {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) (a : ℝ) :
    form F (monomial k a) = a * coef F k := by
  have h1 : (monomial k a : MvPolynomial ι ℝ) = a • basisMonomials ι ℝ k := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h1, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]

theorem exists_form (ι : Type) [Fintype ι] (D : ℕ) (F : (Fin (D + 1) → ι) → ℝ)
    (hF : ∀ (f : Fin (D + 1) → ι) (σ : Equiv.Perm (Fin (D + 1))), F (f ∘ σ) = F f) :
    ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ,
      (∀ n : ι → ℝ, Φ (GlobalTheory.ArInt.lin n ^ (D + 1)) = ∑ f : Fin (D + 1) → ι, (∏ j, n (f j)) * F f) ∧
      ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0 := by
  refine ⟨form F, fun n => ?_, fun P d hd hP => ?_⟩
  · rw [lin_pow, map_sum]
    exact Finset.sum_congr rfl fun f _ => by rw [form_monomial, coef_cnt F hF]
  · rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hdeg : k.degree = d := by
      have := hP (mem_support_iff.1 hk)
      rw [Finsupp.degree_eq_weight_one]; exact this
    rw [form_monomial, coef_of_degree_ne F (by rw [hdeg]; exact hd), mul_zero]

end GlobalTheory.CompanionTheory.Polarisation
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaFin

theorem exists_unip_mul_lev {R : Type} [CommRing R] (r s : ℕ) (P : GL (Fin (r + s)) R)
    (h1 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (P : Matrix _ _ R) i j = 0)
    (h2 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → ((P⁻¹ : GL _ R) : Matrix _ _ R) i j = 0) :
    ∃ (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R), P = unip x * lev R r s m := by
  set e := GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) with he
  set Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := (P : Matrix _ _ R).submatrix e e with hQd
  set Q' : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := ((P⁻¹ : GL _ R) : Matrix _ _ R).submatrix e e with hQ'd
  have hQQ : Q * Q' = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hQQ' : Q' * Q = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hz : Q.toBlocks₂₁ = 0 := by
    ext i j
    exact h1 _ _ (by simp [he]) (by simp [he])
  have hz' : Q'.toBlocks₂₁ = 0 := by
    ext i j
    exact h2 _ _ (by simp [he]) (by simp [he])
  have hb : Q = fromBlocks Q.toBlocks₁₁ Q.toBlocks₁₂ 0 Q.toBlocks₂₂ := by
    rw [← hz, fromBlocks_toBlocks]
  have hb' : Q' = fromBlocks Q'.toBlocks₁₁ Q'.toBlocks₁₂ 0 Q'.toBlocks₂₂ := by
    rw [← hz', fromBlocks_toBlocks]
  generalize Q.toBlocks₁₁ = A at hb
  generalize Q.toBlocks₁₂ = B at hb
  generalize Q.toBlocks₂₂ = D at hb
  generalize Q'.toBlocks₁₁ = A' at hb'
  generalize Q'.toBlocks₁₂ = B' at hb'
  generalize Q'.toBlocks₂₂ = D' at hb'
  rw [hb, hb', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hQQ hQQ'
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ'
  obtain ⟨a1, -, -, d1⟩ := hQQ
  obtain ⟨a2, -, -, d2⟩ := hQQ'
  let X : Matrix (Fin r) (Fin s) R := B * D'
  let x : BlockIx (r + s) r → R := fun p =>
    X ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩
  let m : GL (Fin r) R × GL (Fin s) R := (⟨A, A', a1, a2⟩, ⟨D, D', d1, d2⟩)
  refine ⟨x, m, Units.ext ?_⟩
  have hn : (nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e = fromBlocks 0 X 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [nilM, he]
    · have h : (((e (Sum.inl i) : Fin (r + s)) : ℕ) < r ∧ r ≤ ((e (Sum.inr j) : Fin (r + s)) : ℕ)) := by
        simp [he]
      simp only [submatrix_apply, nilM, of_apply, dif_pos h, fromBlocks_apply₁₂, x]
      congr 1
      exact Fin.ext (by simp [he])
    · simp [nilM, he]
    · simp [nilM, he]
  have hu : ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks 1 X 0 1 := by
    change (1 + nilM x : Matrix _ _ R).submatrix e e = _
    have h : (1 + nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e =
        (1 : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e + (nilM x).submatrix e e := rfl
    rw [h, Matrix.submatrix_one_equiv, hn, ← fromBlocks_one, fromBlocks_add]
    simp
  have hl : ((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks A 0 0 D := by
    rw [lev, GlobalTheory.SmGL.val_emb₂]
    ext i j
    simp [m, ← he]
  have hinj : ∀ M N : Matrix (Fin (r + s)) (Fin (r + s)) R, M.submatrix e e = N.submatrix e e → M = N := by
    intro M N h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa using this
  apply hinj
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ e, hu, hl, fromBlocks_multiply, ← hQd, hb]
  simp [X, Matrix.mul_assoc, d2]

theorem exists_unip_lev_integral (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ)
    (k : GL (Fin (r + s)) (Af E)) :
    ∃ (x : BlockIx (r + s) r → Af E) (m : GL (Fin r) (Af E) × GL (Fin s) (Af E)) (c : GL (Fin (r + s)) (Af E)),
      c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (r + s) ∧ k = unip x * lev (Af E) r s m * c := by
  classical
  let φ := GroundTheory.Automorphic.AdelicGLn.finiteRestrictedEquiv E (r + s)
  let β : Fin (r + s) → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hβ : Monotone β := by
    intro i j hij
    have : (i : ℕ) ≤ j := hij
    simp only [β]
    split_ifs <;> omega
  have loc : ∀ v : HeightOneSpectrum (𝓞 E), ∃ p ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β,
      ∃ c ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s),
        (φ k v : GL (Fin (r + s)) (v.adicCompletion E)) = p * c ∧
        (φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) → p = 1) := by
    intro v
    by_cases h : φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s)
    · exact ⟨1, one_mem _, φ k v, h, (one_mul _).symm, fun _ => rfl⟩
    · obtain ⟨p, hp, c, hc, e⟩ := GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL
        (v.adicCompletion E) (r + s) hβ (φ k v)
      exact ⟨p, hp, c, hc, e, fun h' => absurd h' h⟩
  choose p hp c hc hk h1 using loc
  let P' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨p, by
      filter_upwards [(φ k).2] with v hv
      rw [h1 v hv]
      exact one_mem _⟩
  let C' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨c, Filter.Eventually.of_forall hc⟩
  have hs : ∀ y, φ (φ.symm y) = y := fun y => φ.apply_symm_apply y
  have hPC : k = φ.symm P' * φ.symm C' := by
    apply φ.injective
    rw [map_mul, hs, hs]
    ext v : 1
    exact hk v
  have hPv : ∀ v, φ (φ.symm P') v = p v := fun v => by rw [hs]; rfl
  have hzero : ∀ (q : GL (Fin (r + s)) (Af E)),
      (∀ v, φ q v ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (q : Matrix _ _ (Af E)) i j = 0 := by
    intro q hq i j hi hj
    refine FiniteAdeleRing.ext _ fun v => ?_
    have hlt : β j < β i := by simp [β, hj, Nat.not_lt.2 hi]
    exact hq v hlt
  obtain ⟨x, m, hxm⟩ := exists_unip_mul_lev r s (φ.symm P')
    (hzero _ fun v => by rw [hPv]; exact hp v)
    (hzero _ fun v => by
      rw [map_inv, RestrictedProduct.inv_apply, hPv]
      exact inv_mem (hp v))
  refine ⟨x, m, φ.symm C', ?_, by rw [hPC, hxm]⟩
  rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff_forall]
  intro v
  have : φ (φ.symm C') v = c v := by rw [hs]; rfl
  change φ (φ.symm C') v ∈ _
  rw [this]
  exact hc v

end GlobalTheory.CompanionTheory.CTFin.IwaFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankEqProdOfNonemptyEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WhitRank

theorem finrank_piTensorProduct_eq_prod {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  open Module in
  rw [Module.finrank_eq_nat_card_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (E i)),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => (Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis ℂ (E i))).symm

theorem finrank_eq_prod_of_nonempty_equiv {ι A : Type} [Fintype ι] [AddCommGroup A] [Module ℂ A] (E : ι → Type)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (e : Nonempty (A ≃ₗ[ℂ] ⨂[ℂ] i, E i)) :
    Module.finrank ℂ A = ∏ i, Module.finrank ℂ (E i) := by
  obtain ⟨f⟩ := e
  rw [f.finrank_eq, finrank_piTensorProduct_eq_prod]

theorem whitRankProd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], WhitHeredity k → WhitRankProd k := by
  intro k _ _ _ _ hW ψ hψ hψ1 h N x hd
  obtain ⟨f⟩ := hW ψ hψ hψ1 h N (fun a => (x a).fst) hd (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  exact finrank_eq_prod_of_nonempty_equiv _ ⟨f⟩

end GlobalTheory.CompanionTheory.WhitRank

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInductionStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_finite_by_induction : (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspFin E a) → (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r) → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GenFin E a := by
  first | exact @GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | exact GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | (intros; apply GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters <;> assumption)
end


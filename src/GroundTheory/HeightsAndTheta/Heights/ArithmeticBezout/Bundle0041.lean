import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeChartArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem integral_indicator_ball_norm_pow (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by
  have hfun : (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) =
      fun t => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) ‖t‖ := by
    ext t
    simp [Set.indicator]
  rw [hfun, integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) r)]
  have hvol : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y = R ^ (2 * e + 2) / (2 * e + 2) := by
    have hpt : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
        (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y) =
        (Iio R).indicator (fun y : ℝ => y ^ (2 * e + 1)) := by
      ext y
      by_cases hy : y < R
      · simp [Set.indicator, hy, Complex.finrank_real_complex, pow_succ]
        ring
      · simp [Set.indicator, hy]
    rw [hpt, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR, integral_pow]
    push_cast
    ring_nf
  rw [hint, hvol, Complex.finrank_real_complex]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem le_of_isArithVar_pblk {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    d ≤ n := by
  have h := ringKrullDim_quotient_le P
  rw [hP.2.2.2, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at h
  have hc : Nat.card (Σ k : Unit, PBlk n k) = n := by
    simp [Nat.card_eq_fintype_card]
  rw [hc, Fintype.card_unit] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + n : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h
  have h'' : d + 1 ≤ 1 + n := by exact_mod_cast h'
  omega

theorem integral_chosenSheet_eq {n e : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (g : (Fin n → ℂ) → ℝ) (hg : ∀ (c : ℂ) (z : Fin n → ℂ), c ≠ 0 → g (c • z) = g z)
    (x : Fin e → ℂ) (w : ((k : Unit) → PBlk n k) → ℂ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * chartGramDensity P Ψ S g x w := by
  classical
  by_cases hγ : ∃ γ, IsSheet P Ψ x w γ
  · have hc : chosenSheet P Ψ x w = hγ.choose := by
      simp only [chosenSheet, dif_pos hγ]
    have hd : chartGramDensity P Ψ S g x w = g (fun i => hγ.choose x ⟨(), i⟩) *
        ((e.factorial : ℝ) / Real.pi ^ e *
            gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) x /
          ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose x ⟨(), i⟩)‖ ^ (2 * (e + 1))) := by
      simp only [chartGramDensity, dif_pos hγ]
    rw [hc, hd]
    set u : Fin n → ℂ := fun i => hγ.choose x ⟨(), i⟩ with hu_def
    set G := gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) x with hG_def
    have hmem : hγ.choose x ∈ mcPts P := (hγ.choose_spec.2.self_of_nhds).2.1
    have hu : u ≠ 0 := by
      obtain ⟨i, hi⟩ := hmem.1 ()
      intro h
      exact hi (congrFun h i)
    have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
    have hinv : S⁻¹ *ᵥ (S *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hdet, Matrix.one_mulVec]
    have hSu : S *ᵥ u ≠ 0 := by
      intro h
      apply hu
      rw [← hinv, h, Matrix.mulVec_zero]
    set ρ := ‖WithLp.toLp 2 (S *ᵥ u)‖ with hρ_def
    have hρ : 0 < ρ := by
      rw [hρ_def, norm_pos_iff]
      intro h
      exact hSu (by simpa using congrArg WithLp.ofLp h)
    have hpt : ∀ t : ℂ, (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ u)) =
        t • u := by
      intro t
      have : (fun i => (t • WithLp.toLp 2 (S *ᵥ u)) i) = t • (S *ᵥ u) := by
        ext i
        simp
      simp only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose, this,
        Matrix.mulVec_smul, hinv]
    have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ u)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
        fun t => (g u * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
      have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [h0] with t ht
      have hiff : ‖t • WithLp.toLp 2 (S *ᵥ u)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
        rw [norm_smul, lt_div_iff₀ hρ]
      by_cases hb : ‖t‖ < 1 / ρ
      · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
          indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t u ht]
        ring
      · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
          indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
        ring
    rw [integral_congr_ae hae, integral_const_mul,
      integral_indicator_ball_norm_pow e (by positivity)]
    rw [one_div, inv_pow, Nat.factorial_succ]
    have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have hc : chosenSheet P Ψ x w = 0 := by
      simp only [chosenSheet, dif_neg hγ]
    have hd : chartGramDensity P Ψ S g x w = 0 := by
      simp only [chartGramDensity, dif_neg hγ]
    have hG : gramVol (fun x' => S *ᵥ fun i =>
        (0 : (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ) x' ⟨(), i⟩) x = 0 := by
      have hz : (S *ᵥ fun _ : Fin n => (0 : ℂ)) = 0 := Matrix.mulVec_zero S
      have hw : ∀ a : Fin (e + 1), (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) :
          Fin (e + 1) → Fin n → ℂ) a = 0 := fun a => Fin.cases rfl (fun _ => rfl) a
      simp [gramVol, hz, hw]
      rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 from rfl,
        Matrix.det_zero, Complex.zero_re]
    rw [hc, hd, hG]
    simp

theorem ConeChartArea.proof (hA : ConeSheetArea.Statement) : ConeChartArea.Statement := by
  intro n e S hS P Ψ g hP hΨ _hgm hdeg hint
  set C := coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) with hC
  set f : EuclideanSpace ℂ (Fin n) → ℝ := (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
    (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y)) with hf
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P,
      eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0} = C ∩ ball 0 1 := by
    ext y
    simp only [hC, coneSet, mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
    exact and_comm
  have hfC : IntegrableOn f C (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [IntegrableOn, hf, integrable_indicator_iff measurableSet_ball, IntegrableOn,
      Measure.restrict_restrict measurableSet_ball, inter_comm]
    rw [hset] at hint
    exact hint
  have key := hA n e S hS P Ψ f hP hΨ hfC
  have hterm : ∀ x : Fin e → ℂ, (∑ᶠ w ∈ fibre P Ψ x, ∫ t : ℂ,
      f (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        ∑ᶠ w ∈ fibre P Ψ x, chartGramDensity P Ψ S g x w := by
    intro x
    rw [mul_finsum_mem]
    exact finsum_mem_congr rfl fun w _ => integral_chosenSheet_eq S hS P Ψ g hdeg x w
  simp_rw [hterm, integral_const_mul] at key
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_isArithVar_pblk hP)
  have hM : 0 < (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal :=
    ENNReal.toReal_pos hM0.ne' hMtop.ne
  have hc : (0 : ℝ) < Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) := by positivity
  have hleft : ∫ y in C, f y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫ y in {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P,
        eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0},
        g ((ObjectsHeight.ofPointMatrix S hS).pointOf y)
          ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [hf, setIntegral_indicator measurableSet_ball, hset]
  rw [hleft] at key
  unfold coneIntegral
  rw [div_eq_iff hM.ne']
  have key' := key
  rw [mul_left_comm] at key'
  have := mul_left_cancel₀ hc.ne' key'
  rw [this, mul_comm]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecFiniteUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Vertical

noncomputable section

namespace SecFiniteUnit

theorem prod_natDegree_coeff {R ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R)
    (D : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, D i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (f i).coeff (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le_of_le ha' h1,
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' h1, h2]⟩

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}

def lineSub (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial R :=
  Fin.cases (motive := fun _ => Polynomial R)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def lineTop (y : Par e n → R) (ij : Fin (e + 1) × Fin n) : R :=
  Fin.cases (motive := fun _ => R) (y (.inr ij.2)) (fun i => y (.inl (i, ij.2))) ij.1

theorem lineSub_natDegree_le (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).natDegree ≤ groupWeight (e + 1) n ij 0 := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    · split_ifs <;> simp
  | succ i => simp [lineSub]

theorem lineSub_coeff (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).coeff (groupWeight (e + 1) n ij 0) = lineTop y ij := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, lineTop, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    split_ifs <;> simp [Polynomial.coeff_one]
  | succ i => simp [lineSub, lineTop, groupWeight, Fin.succ_ne_zero]

theorem weight_sum {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    {d : Fin (e + 1) × Fin n →₀ ℕ} (hd : coeff d g ≠ 0) :
    ∑ ij, d ij * groupWeight (e + 1) n ij 0 = δ := by
  have h := congrFun (hg hd) 0
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simpa [Finset.sum_apply, smul_eq_mul] using h

theorem lineSub_aeval {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    (y : Par e n → R) (m : Fin n) :
    (aeval (lineSub y m) g).natDegree ≤ δ ∧
      (aeval (lineSub y m) g).coeff δ =
        eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) := by
  have hprod : ∀ d ∈ g.support, (∏ ij, lineSub y m ij ^ d ij).natDegree ≤ δ ∧
      (∏ ij, lineSub y m ij ^ d ij).coeff δ = ∏ ij, lineTop y ij ^ d ij := by
    intro d hd
    have h := prod_natDegree_coeff Finset.univ (fun ij => lineSub y m ij ^ d ij)
      (fun ij => d ij * groupWeight (e + 1) n ij 0)
      (fun ij _ => Polynomial.natDegree_pow_le_of_le _ (lineSub_natDegree_le y m ij))
    rw [weight_sum hg (mem_support_iff.mp hd)] at h
    refine ⟨h.1, h.2.trans (Finset.prod_congr rfl fun ij _ => ?_)⟩
    rw [Polynomial.coeff_pow_of_natDegree_le (lineSub_natDegree_le y m ij), lineSub_coeff]
  rw [aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hprod d hd).1, ?_⟩
  have hspec : eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) = aeval (lineTop y) g := by
    rw [specRest, eval₂_comp_left, aeval_def]
    congr 1
    · ext a; simp
    · funext ⟨i, j⟩
      induction i using Fin.cases with
      | zero => simp [lineTop]
      | succ i => simp [lineTop]
  rw [hspec, aeval_def, eval₂_eq', Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, (hprod d hd).2]

theorem coord_integral {δ : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → R)
    (hg : IsChowForm Q (e + 1) g) (hδ : IsMultiHomog δ g)
    (hu : IsUnit (eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y))) (m : Fin n) :
    IsIntegral R (secCoord (Q.map (MvPolynomial.map (algebraMap k R))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k R))
  set x := secCoord Q' y with hx
  have hC : ∀ a : R, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap R (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k R) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap R (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h
    simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap R (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ Vertical.incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices Vertical.incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap R (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
          Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := IncidenceNull.full k n (e + 1) Q g hg
  set P : Polynomial R := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj

  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hdeg, hcoeff⟩ := lineSub_aeval hδ y m
  obtain ⟨u, hu'⟩ := hu
  have hmonic : (Polynomial.C ((u⁻¹ : Rˣ) : R) * P).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one δ
      ((Polynomial.natDegree_C_mul_le _ _).trans hdeg)
      (by rw [Polynomial.coeff_C_mul, hcoeff, ← hu', Units.inv_mul])
  refine ⟨(Polynomial.C ((u⁻¹ : Rˣ) : R) * P) ^ N, hmonic.pow N, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, map_mul, mul_pow, hN, mul_zero]

end SecFiniteUnit

theorem SecFiniteUnit.proof : SecFiniteUnit.Statement := by
  intro k R _ _ _ n e δ Q g y hg hδ hu
  set Q' := Q.map (MvPolynomial.map (algebraMap k R))
  have htop : Algebra.adjoin R (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ R (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective R _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecFiniteUnit.coord_integral Q g y hg hδ hu m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights
end


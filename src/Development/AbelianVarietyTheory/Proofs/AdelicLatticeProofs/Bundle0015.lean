import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixEntriesBoundedOfHermitianLogTraceSqLe
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma energy_entry_sq_le {ι : Type} [Fintype ι] (x : Matrix ι ι ℂ) (i j : ι) :
    ‖x i j‖ ^ 2 ≤ (Matrix.trace (xᴴ * x)).re := by
  have h : (Matrix.trace (xᴴ * x)).re = ∑ b, ∑ a, ‖x a b‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [h]
  calc ‖x i j‖ ^ 2 ≤ ∑ a, ‖x a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ‖x a j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun b => ∑ a, ‖x a b‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

private lemma energy_trace_conj {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (d : ι → ℝ) : (Matrix.trace (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)).re = ∑ i, d i := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.trace_mul_cycle, hU', one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem entries_le_of_energy_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by
  intro ι _ _ E
  refine ⟨max (√E) (√(Fintype.card ι * Real.exp (√E))), ?_⟩
  rintro x H ⟨U, d, hU, hH, hA⟩ hE i j
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hherm : Hᴴ = H := by
    rw [hH]
    simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]
  have hHH : H * H = U * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hH]
    calc U * diagonal (fun i => (d i : ℂ)) * Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)
        = U * (diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          congr 3
          funext k
          push_cast
          ring
  have hd : ∀ k, d k ≤ √E := by
    intro k
    have h1 : ∑ k, d k ^ 2 ≤ E := by
      rw [hHH, energy_trace_conj U hU] at hE
      exact hE
    have h2 : d k ^ 2 ≤ ∑ k, d k ^ 2 :=
      Finset.single_le_sum (f := fun k => d k ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
    exact Real.le_sqrt_of_sq_le (h2.trans h1)
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le x i j).trans ?_
    rw [hA, energy_trace_conj U hU (fun i => Real.exp (d i))]
    calc ∑ k, Real.exp (d k) ≤ ∑ _k : ι, Real.exp (√E) :=
          Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (hd k)
      _ = _ := by simp
  · refine le_trans ?_ (le_max_left _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le H i j).trans ?_
    rwa [hherm]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]

omit [Fintype ι] in
theorem tpow_diagonal_alg (n : ℕ) (a : ι → R) :
    tpow n (diagonal a) = diagonal (fun b : Fin n → ι => ∏ j, a (b j)) := by
  ext b c
  simp only [tpow, Matrix.of_apply]
  by_cases h : b = c
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Matrix.diagonal_apply_ne _ hj)

omit [Fintype ι] in
theorem tpow_one_alg (n : ℕ) : tpow n (1 : Matrix ι ι R) = 1 := by
  have h := tpow_diagonal_alg (ι := ι) n (fun _ => (1 : R))
  simpa using h

omit [DecidableEq ι] in
theorem tpow_mul_alg (n : ℕ) (y z : Matrix ι ι R) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext b c
  simp only [tpow, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]

theorem act_apply_alg {m : ℕ} (d : Fin m → ℕ) (t : TIdx ι d → R) (y : Matrix ι ι R) (k : TIdx ι d) :
    act d t y k = ∑ a : Fin (d k.1) → ι, t ⟨k.1, a⟩ * ∏ j, y (a j) (k.2 j) := by
  simp [act, tpow, Matrix.vecMul, dotProduct]

end

theorem tpow_act_algebra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R], (∀ n : ℕ, tpow n (1 : Matrix ι ι R) = 1 ∧ (∀ y z : Matrix ι ι R, tpow n (y * z) = tpow n y * tpow n z) ∧ ∀ y : Matrix ι ι R, (tpow n y)ᵀ = tpow n yᵀ) ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → R), act d t 1 = t ∧ (∀ y z : Matrix ι ι R, act d t (y * z) = act d (act d t y) z) ∧ (∀ (a : ι → R) (k : TIdx ι d), act d t (diagonal a) k = t k * ∏ j, a (k.2 j)) ∧ (∀ (S : Subring R) (y : Matrix ι ι R), (∀ k, t k ∈ S) → (∀ i j, y i j ∈ S) → ∀ k, act d t y k ∈ S) ∧ (∀ (c : R) (y : Matrix ι ι R), act d (c • t) y = c • act d t y) ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (y : Matrix ι ι R), act d (fun k => φ (t k)) (y.map φ) = fun k => φ (act d t y k) := by
  intro ι _ _ R _
  refine ⟨fun n => ⟨tpow_one_alg n, tpow_mul_alg n, fun y => ?_⟩, fun m d t => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · ext a b
    simp [tpow]
  · funext k
    simp [act, tpow_one_alg]
  · intro y z
    funext k
    simp only [act, tpow_mul_alg, ← Matrix.vecMul_vecMul]
  · intro a k
    simp only [act, tpow_diagonal_alg, Matrix.vecMul_diagonal]
  · intro S y ht hy k
    rw [act_apply_alg]
    exact S.sum_mem fun a _ => S.mul_mem (ht _) (S.prod_mem fun j _ => hy _ _)
  · intro c y
    funext k
    simp only [act_apply_alg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · intro R' _ φ y
    funext k
    simp only [act_apply_alg, map_sum, map_mul, map_prod, Matrix.map_apply]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeAlgebraMapOfIsNilpotentTmulSub
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_algHom_algebraicClosure_ker_le (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[K] AlgebraicClosure K, ∀ x, φ x = 0 → x ∈ m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ι : (A ⧸ m) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨ι.comp (Ideal.Quotient.mkₐ K m), fun x hx => ?_⟩
  have h : ι (Ideal.Quotient.mk m x) = 0 := hx
  have h2 : Ideal.Quotient.mk m x = 0 := ι.toRingHom.injective (by simpa using h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem mem_range_algebraMap_of_isNilpotent_tmul_sub (K A : Type) [Field K] [CharZero K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsReduced A] (f : A)
    (hf : IsNilpotent (f ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] f)) : f ∈ (algebraMap K A).range := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have h1 : ∀ φ ψ : A →ₐ[K] AlgebraicClosure K, φ f = ψ f := by
    intro φ ψ
    have h := (hf.map (Algebra.TensorProduct.productMap φ ψ)).eq_zero
    simpa [sub_eq_zero] using h
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -⟩ := exists_algHom_algebraicClosure_ker_le K A m₀
  have h2 : φ₀ f ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    exact h1 (σ.toAlgHom.comp φ₀) φ₀
  obtain ⟨c, hc⟩ := h2
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  refine ⟨c, ?_⟩
  have h3 : f - algebraMap K A c ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_algebraicClosure_ker_le K A m
    apply hφ
    rw [map_sub, AlgHom.commutes, hc, h1 φ φ₀, sub_self]
  have h4 : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [h4, Ideal.mem_bot, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MulLogEqNegLogMul
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mul_diagonal_eq_neg_of_exp {ι : Type} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) (d d' : ι → ℝ)
    (h : diagonal (fun i => (Real.exp (d' i) : ℂ)) * y * diagonal (fun i => (Real.exp (d i) : ℂ)) = y) :
    y * diagonal (fun i => (d i : ℂ)) = -(diagonal (fun i => (d' i : ℂ)) * y) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at hij
  rw [neg_apply, mul_diagonal, diagonal_mul]
  by_cases hy : y i j = 0
  · simp [hy]
  · have h1 : ((Real.exp (d' i) : ℝ) : ℂ) * (Real.exp (d j) : ℝ) = 1 := by
      apply mul_left_cancel₀ hy
      linear_combination hij
    have h2 : Real.exp (d' i + d j) = 1 := by
      rw [Real.exp_add]
      exact_mod_cast h1
    have h3 : d' i + d j = 0 := by simpa using h2
    have h4 : (d' i : ℂ) + (d j : ℂ) = 0 := by exact_mod_cast h3
    linear_combination (y i j) * h4

theorem mul_log_eq_neg_log_mul : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  intro ι _ _ x x' H H' ⟨U, d, hU, hH, hA⟩ ⟨V, d', hV, hH', hA'⟩ hx
  have hx' : x * x' = 1 := mul_eq_one_comm.mp hx
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have key : (x'ᴴ * x') * x * (xᴴ * x) = x := by
    calc (x'ᴴ * x') * x * (xᴴ * x) = x'ᴴ * (x' * x) * xᴴ * x := by simp only [Matrix.mul_assoc]
      _ = (x * x')ᴴ * x := by rw [hx, Matrix.mul_one, conjTranspose_mul]
      _ = x := by rw [hx', conjTranspose_one, Matrix.one_mul]
  rw [hA, hA'] at key
  have hy := mul_diagonal_eq_neg_of_exp (Vᴴ * x * U) d d' (by
    calc _ = (Vᴴ * V) * diagonal (fun i => (Real.exp (d' i) : ℂ)) * (Vᴴ * x * U) *
            diagonal (fun i => (Real.exp (d i) : ℂ)) * (Uᴴ * U) := by
          rw [hV', hU', Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (Real.exp (d' i) : ℂ)) * Vᴴ * x *
            (U * diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ)) * U := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * x * U := by rw [key])
  calc x * H = (V * Vᴴ) * x * H := by rw [hV, Matrix.one_mul]
    _ = V * (Vᴴ * x * U * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = -(H' * x * (U * Uᴴ)) := by
        rw [hy, hH']; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    _ = -(H' * x) := by rw [hU, Matrix.mul_one]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneAddSmulMemOfSqZero
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_poly_ev_line {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℚ)
    (A B : Matrix ι ι ℂ) : ∃ p : Polynomial ℂ, ∀ t : ℂ, p.eval t = ev f (A + t • B) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C (algebraMap ℚ ℂ a), fun t => by simp [ev]⟩
  | add f g hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    refine ⟨p + q, fun t => ?_⟩
    rw [Polynomial.eval_add, hp, hq]
    simp [ev]
  | mul_X f ij hf =>
    obtain ⟨p, hp⟩ := hf
    refine ⟨p * (Polynomial.C (A ij.1 ij.2) + Polynomial.X * Polynomial.C (B ij.1 ij.2)), fun t => ?_⟩
    rw [Polynomial.eval_mul, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    simp [ev]

theorem one_add_smul_mem_of_sq_zero :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ →
      ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  intro ι _ _ Γ hΓ ε hε h1 t
  have hn : ∀ n : ℕ, 1 + (n : ℂ) • ε ∈ Γ := by
    intro n
    induction n with
    | zero => simpa using hΓ.one_mem
    | succ n ih =>
      have h := hΓ.mul_mem _ ih _ h1
      have e : (1 + (n : ℂ) • ε) * (1 + ε) = 1 + ((n + 1 : ℕ) : ℂ) • ε := by
        rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hε, smul_zero, add_zero, Nat.cast_succ,
          add_smul, one_smul, add_assoc]
      rwa [e] at h
  apply hΓ.closed
  intro f hf
  obtain ⟨p, hp⟩ := exists_poly_ev_line f 1 ε
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective ?_
    intro n
    show p.eval (n : ℂ) = 0
    rw [hp]
    exact hf _ (hn n)
  rw [← hp, hp0, Polynomial.eval_zero]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdAbsNormPowValuationTwoLe
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem prod_absNorm_pow_le_two_pow :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  intro F _ _ S e h
  have hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    intro v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    have h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2 :=
      HeightOneSpectrum.valuation_of_algebraMap v 2
    rw [map_ofNat, h v hv] at h2
    exact h2.ge
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro v _ w _ hvw
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun hh => hvw (HeightOneSpectrum.ext hh))
  have hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hn, map_prod] at h3
  simp only [map_pow] at h3
  exact Nat.le_of_dvd (by positivity) h3

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatPts

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

lemma _root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap {ι R : Type} [CommRing R] [Algebra ℚ R]
    (f : MvPolynomial (ι × ι) ℚ) (γ : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.ev f (γ.map (algebraMap ℚ R)) = algebraMap ℚ R (_root_.GlobalTheory.ClassFin.ev f γ) := by
  unfold _root_.GlobalTheory.ClassFin.ev
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
  intro ι _ _ Γ
  refine ⟨fun γ hγ => ?_, fun R _ _ γ hγ => ?_⟩
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq]
    intro f hf
    have h := hf _ hγ
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap] at h
    exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq] at hγ ⊢
    intro f hf
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap, hγ f hf, map_zero]

end GlobalTheory.ClassFin.RatPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexHigherUnitsSuccLeCard
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < WithZero.exp m) :
    a ≤ WithZero.exp (m - 1) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem relIndex_hiUnits_succ_le :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ),
      w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) →
      (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧
        (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  intro K _ w π R n hπ hR
  have hπn : w (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hπn0 : w (π ^ n) ≠ 0 := by rw [hπn]; exact WithZero.exp_ne_zero
  have hπn0' : π ^ n ≠ 0 := by
    intro h; rw [h] at hπn0; simp at hπn0
  have hex : ∀ x : hiUnits w n, ∃ r : R, w ((((x : Kˣ) : K) - 1) / π ^ n - r) < 1 := by
    intro x
    have hx : w (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := x.2.2
    obtain ⟨r, hr, h⟩ := hR ((((x : Kˣ) : K) - 1) / π ^ n) (by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hπn0), hπn]; exact hx)
    exact ⟨⟨r, hr⟩, h⟩
  choose f hf using hex
  have key : ∀ x y : hiUnits w n, f x = f y →
      x⁻¹ * y ∈ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) := by
    intro x y hxy
    have hx1 : w ((x : Kˣ) : K) = 1 := x.2.1
    have hy1 : w ((y : Kˣ) : K) = 1 := y.2.1
    have h1 := hf x
    have h2 := hf y
    rw [← hxy] at h2
    have h3 := w.map_sub_lt h2 h1
    have h4 : (((y : Kˣ) : K) - 1) / π ^ n - (f x : K) -
        ((((x : Kˣ) : K) - 1) / π ^ n - (f x : K)) =
        (((y : Kˣ) : K) - ((x : Kˣ) : K)) / π ^ n := by ring
    rw [h4, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hπn0), hπn] at h3
    have h5 := le_exp_sub_one_of_lt_exp h3
    rw [Subgroup.mem_subgroupOf]
    have hv : ((((x⁻¹ * y : hiUnits w n) : Kˣ)) : K) =
        ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) := by simp
    refine ⟨by rw [hv, map_mul, map_inv₀, hx1, hy1]; simp, ?_⟩
    have hx0 : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h6 : ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) - 1 =
        ((x : Kˣ) : K)⁻¹ * (((y : Kˣ) : K) - ((x : Kˣ) : K)) := by
      field_simp
    rw [hv, h6, map_mul, map_inv₀, hx1, inv_one, one_mul]
    refine h5.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hinj : Function.Injective
      (fun q : hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) => f q.out) := by
    intro p q hpq
    have := key _ _ hpq
    rw [← QuotientGroup.eq] at this
    simpa using this
  have hfin : Finite (hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n)) :=
    Finite.of_injective _ hinj
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := R), Fintype.card_coe] at this
    exact this

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexNormMulRelIndexSqsKer
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem relIndex_norm_mul_relIndex_sqs_ker :
    ∀ (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) := by
  intro A _ σ hσ h90
  set N : A →* A := MonoidHom.id A * σ with hN
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  let f : A →* A := MonoidHom.id A / σ
  have hNa : ∀ a, N a = a * σ a := fun a => rfl
  have hfa : ∀ a, f a = a / σ a := fun a => rfl
  have hBa : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have hK : ∀ a, a ∈ N.ker ↔ a * σ a = 1 := fun a => Iff.rfl
  have hsq : ∀ (U : Subgroup A) (a : A), a ∈ sqs U ↔ ∃ b ∈ U, b ^ 2 = a := fun U a => Iff.rfl
  have h1 : sqs B ≤ N.range := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (hsq _ _).1 ha
    exact ⟨b, by rw [hNa, (hBa b).1 hb, sq]⟩
  have h2 : N.range ≤ B := by
    rintro _ ⟨a, rfl⟩
    rw [hBa, hNa, map_mul, hσ, mul_comm]
  have h3 : f.range = N.ker := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      rw [hK, hfa, map_div, hσ]
      simp
    · intro ha
      obtain ⟨b, hb⟩ := h90 a ((hK a).1 ha)
      exact ⟨b, hb.symm⟩
  have h4 : (sqs B).comap N = (sqs N.ker).comap f := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hsq, hsq]
    constructor
    · rintro ⟨b, hb, hab⟩
      rw [hBa] at hb
      rw [hNa] at hab
      refine ⟨a / b, ?_, ?_⟩
      · rw [hK, map_div, hb, div_mul_div_comm, ← hab, sq, div_self']
      · rw [hfa, div_pow, hab, sq, mul_div_mul_left_eq_div]
    · rintro ⟨c, hc, hac⟩
      rw [hK] at hc
      rw [hfa] at hac
      have hc' : σ c = c⁻¹ := eq_inv_of_mul_eq_one_right hc
      have ha' : σ a = a / c ^ 2 := by rw [hac]; simp
      refine ⟨a / c, ?_, ?_⟩
      · rw [hBa, map_div, hc', ha', sq, div_inv_eq_mul, div_mul_eq_div_div, div_mul_cancel]
      · rw [hNa, ha', div_pow, sq a, mul_div_assoc]
  have h5 : (sqs B).relIndex N.range = (sqs N.ker).relIndex N.ker := by
    rw [← Subgroup.index_comap, h4, Subgroup.index_comap, h3]
  rw [← h5, mul_comm]
  exact Subgroup.relIndex_mul_relIndex _ _ _ h1 h2

end GlobalTheory.QNorm
end


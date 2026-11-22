import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem XBound.intersectionNumber_baseChange : XBound.Statement := by
  intro r a hN
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · simp only [restX]
    push_cast
    push_cast at hN'
    nlinarith [sq_nonneg ((r : ℝ) - a)]
  · nlinarith

theorem XOverPrime.intersectionNumber_baseChange : XOverPrime.Statement := by
  intro f r a B₀ p hf hN hB hp
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hX := (XBound.intersectionNumber_baseChange r a hN)
  have hX2 : (restX r a : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := hX.1.trans hX.2
  have hN2 : 0 < ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hp4 : 4 * ((r + a : ℕ) : ℝ) ^ 2 < p := by nlinarith
  have hp0 : 0 < p := lt_trans (by positivity) hp4
  rw [div_le_iff₀ hp0]
  nlinarith

theorem two_log_four_le : 2 * Real.log 4 ≤ 2.78 := by
  have := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  nlinarith

theorem RestConstants.intersectionNumber_baseChange : RestConstants.Statement := by
  refine ⟨two_log_four_le, ?_⟩
  intro f N hf hN
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have : (1.5 : ℝ) * f * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) =
      1.5 * (3 / 2) * 2.78 / 4 := by
    field_simp
  rw [this]
  norm_num

theorem SmallRankBound.intersectionNumber_baseChange : SmallRankBound.Statement := by
  intro k m j' N hm hk hj hN
  have h3 : 8 ≤ m ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
  have h4 : 8 * m ≤ m ^ 4 := by
    calc 8 * m ≤ m ^ 3 * m := Nat.mul_le_mul_right m h3
      _ = m ^ 4 := by ring
  have hk' : 2 * m + 2 ≤ k := by omega
  exact ⟨hk', by omega⟩

theorem SmallRankWeakHypothesis.intersectionNumber_baseChange : SmallRankWeakHypothesis.Statement := by
  intro h
  have := h 5 2 2 6 le_rfl (by norm_num) le_rfl (by norm_num)
  omega

theorem GeometricTail.intersectionNumber_baseChange : GeometricTail.Statement := by
  intro p k hp hk
  set x : ℝ := (p ^ k)⁻¹ with hx
  have hpk : (2 : ℝ) ≤ p ^ k := by
    calc (2 : ℝ) ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := pow_le_pow_right₀ (by linarith) hk
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hterm : ∀ n : ℕ, (p ^ ((n + 1) * k))⁻¹ = x * x ^ n := by
    intro n
    rw [hx, ← pow_succ', inv_pow, ← pow_mul, mul_comm k]
  have hs : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_lt_one hx0 (by linarith)
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact hs.mul_left x
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]
    have h1 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc x * (1 - x)⁻¹ ≤ x * 2 := mul_le_mul_of_nonneg_left h1 hx0
      _ = 2 * x := by ring

theorem exp_three_eighths_le : Real.exp (3 / 8) ≤ 1.5 := by
  have he := Real.exp_one_lt_d9
  have h8 : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  by_contra hlt
  push Not at hlt
  have h1 : (1.5 : ℝ) ^ 8 < Real.exp (3 / 8) ^ 8 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have h2 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h8] at h1
  norm_num at h1 h2
  linarith

theorem ExponentialTail.intersectionNumber_baseChange : ExponentialTail.Statement := by
  intro p X hp hX hXp
  set u : ℝ := X / p with hu
  have hu0 : 0 ≤ u := by positivity
  have hu38 : u ≤ 3 / 8 := by rw [hu, div_le_iff₀ hp]; linarith
  have hA : 0 ≤ X / p ^ 2 := by positivity
  have hterm : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) =
      X / p ^ 2 * (u ^ k * (2 / ((k + 2).factorial : ℝ))) := by
    intro k
    rw [hu, div_pow]
    field_simp
    ring
  have hfac : ∀ k : ℕ, 2 / ((k + 2).factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
    intro k
    have h1 : (2 : ℝ) * k.factorial ≤ (k + 2).factorial := by
      have : 2 * k.factorial ≤ (k + 2).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hbound : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤
      X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [hterm]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [div_eq_mul_one_div (u ^ k)]
    exact mul_le_mul_of_nonneg_left (hfac k) (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) := by
    intro k; positivity
  have hexp : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial u
  have hsum : Summable (fun k : ℕ => X / p ^ 2 * (u ^ k / (k.factorial : ℝ))) := hexp.mul_left _
  have hS : Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)) :=
    Summable.of_nonneg_of_le hnn hbound hsum
  refine ⟨hS, ?_, ?_⟩
  · calc ∑' k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)
        ≤ ∑' k : ℕ, X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := hS.tsum_le_tsum hbound hsum
      _ = X / p ^ 2 * Real.exp u := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      _ ≤ X / p ^ 2 * Real.exp (3 / 8) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu38) hA
      _ = Real.exp (3 / 8) * X / p ^ 2 := by ring
  · have := exp_three_eighths_le
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right this hA

theorem ChebyshevThetaBound.intersectionNumber_baseChange : ChebyshevThetaBound.Statement := by
  intro x hx
  set n := ⌊x⌋₊
  have hprod : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p =
      Real.log (primorial n) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    exact_mod_cast this.ne'
  rw [hprod]
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n) ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log hpos
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]
    _ ≤ x * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le hx)
        exact Real.log_nonneg (by norm_num)

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

open MvPolynomial

abbrev flagTwoFirstRoot : RootRing 1 (1+1) := X ((0:Fin 1), (0 : Fin (1+1)))
abbrev flagTwoSecondRoot : RootRing 1 (1+1) := X ((0:Fin 1), (1 : Fin (1+1)))

theorem inh_mu_eq : smallBlockMu 1 1 1 .last = flagTwoSecondRoot := by
  simp [smallBlockMu, yRoot, yIndex, SmallBlock.sign]

theorem inh_fib_eq : fibreClass 1 1 1 .last = 1 := by
  simp [fibreClass, vandermondeOf]

theorem inh_F_eq : restPolynomial 1 1 1 .last = flagTwoSecondRoot ^ 2 := by
  simp [restPolynomial, inh_mu_eq, inh_fib_eq]

theorem inh_decomp : IsPowerSumDecomposition 1 (1+1) (restPolynomial 1 1 1 .last)
    (fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0) := by
  have h2 : (C (2⁻¹ : ℚ) : RootRing 1 (1+1)) * 2 = 1 := by
    have : (2 : RootRing 1 (1+1)) = C 2 := (map_ofNat C 2).symm
    rw [this, ← C_mul]; norm_num
  have hI : Finset.Icc 1 (1+1) = ({1, 2} : Finset ℕ) := by decide
  rw [inh_F_eq, IsPowerSumDecomposition, hI]
  simp [blockPowerSum, Fin.sum_univ_two]
  linear_combination (-(flagTwoSecondRoot ^ 2)) * h2

theorem inh_van_eq : blockVandermonde 1 (1+1) = flagTwoFirstRoot - flagTwoSecondRoot := by
  have hIoi0 : Finset.Ioi (0 : Fin (1+1)) = {1} := by decide
  have hIoi1 : Finset.Ioi (1 : Fin (1+1)) = ∅ := by decide
  simp [blockVandermonde, vandermondeOf, Fin.prod_univ_two, hIoi0, hIoi1]

theorem inh_J_eq : fibreDegree 1 1 1 .last = -1 := by
  have hH : smallBlockMu 1 1 1 .last ^ (1 * (1 * 1)) * fibreClass 1 1 1 .last = flagTwoSecondRoot := by
    simp [inh_mu_eq, inh_fib_eq]
  rw [fibreDegree, hH, flagIntegral, inh_van_eq]
  have hne : ((0:Fin 1), (0 : Fin (1+1))) ≠ ((0:Fin 1), (1 : Fin (1+1))) := by decide
  rw [Finset.sum_eq_single (Finsupp.single ((0:Fin 1), (1 : Fin (1+1))) 1)]
  · simp [flagTwoFirstRoot, flagTwoSecondRoot, coeff_X', Finsupp.single_left_inj, hne, hne.symm, Finsupp.single_eq_single_iff]
  · intro b _ hb
    have : coeff b flagTwoSecondRoot = 0 := by
      rw [coeff_X']; exact if_neg (fun h => hb h.symm)
    simp [this]
  · intro h
    have : coeff (Finsupp.single ((0:Fin 1), (1 : Fin (1+1))) 1) (flagTwoFirstRoot - flagTwoSecondRoot) = 0 := by
      simpa using h
    simp [flagTwoFirstRoot, flagTwoSecondRoot, coeff_X', Finsupp.single_eq_single_iff, hne, hne.symm] at this

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Pluecker
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Matrix Finset

open scoped ComplexOrder

noncomputable section

namespace Elem

variable {R : Type*} [CommRing R] {κ : Type*}

def subsetCols {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) : κ :=
  ((S.1.equivFinOfCardEq S.2).symm i : κ)

theorem subsetCols_injective {p : ℕ} (S : {s : Finset κ // s.card = p}) :
    Function.Injective (subsetCols S) := by
  intro i j h
  exact (S.1.equivFinOfCardEq S.2).symm.injective (Subtype.ext h)

theorem subsetCols_mem {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) :
    subsetCols S i ∈ S.1 :=
  ((S.1.equivFinOfCardEq S.2).symm i).2

theorem exists_subsetCols_eq {p : ℕ} (S : {s : Finset κ // s.card = p}) {k : κ}
    (hk : k ∈ S.1) : ∃ i, subsetCols S i = k :=
  ⟨S.1.equivFinOfCardEq S.2 ⟨k, hk⟩, by simp [subsetCols]⟩

theorem det_mul_expand [Fintype κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ φ : Fin p → κ, (A.submatrix id φ).det * ∏ i, B (φ i) i := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib]
  ring

theorem det_submatrix_eq_zero_of_not_injective {p : ℕ} (A : Matrix (Fin p) κ R)
    (φ : Fin p → κ) (h : ¬ Function.Injective φ) : (A.submatrix id φ).det = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

theorem cauchyBinet [Fintype κ] [DecidableEq κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det := by
  rw [det_mul_expand]
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun φ _ h => by
        by_contra hφ
        exact h (by rw [det_submatrix_eq_zero_of_not_injective A φ hφ, zero_mul]))]
  have hpairs : ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det =
      ∑ x : {s : Finset κ // s.card = p} × Equiv.Perm (Fin p),
        (A.submatrix id (subsetCols x.1 ∘ x.2)).det * ∏ i, B (subsetCols x.1 (x.2 i)) i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [det_apply' (B.submatrix _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have : A.submatrix id (subsetCols S ∘ π) =
        (A.submatrix id (subsetCols S)).submatrix id π := rfl
    rw [this, det_permute']
    simp only [submatrix_apply, id]
    ring
  rw [hpairs]
  symm
  refine Finset.sum_bij (fun x _ => subsetCols x.1 ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (subsetCols_injective x.1).comp x.2.injective
  · rintro ⟨S, π⟩ _ ⟨T, π'⟩ _ hxy
    simp only at hxy
    have hST : S = T := by
      apply Subtype.ext
      ext k
      constructor
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq S hk
        have := congrFun hxy (π.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [this]
        exact subsetCols_mem T _
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq T hk
        have := congrFun hxy (π'.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [← this]
        exact subsetCols_mem S _
    subst hST
    have : π = π' := by
      ext i
      exact congrArg Fin.val (subsetCols_injective S (congrFun hxy i))
    rw [this]
  · intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    let S : {s : Finset κ // s.card = p} :=
      ⟨Finset.univ.image φ, by rw [Finset.card_image_of_injective _ hφ]; simp⟩
    let g : Fin p → Fin p := fun i =>
      S.1.equivFinOfCardEq S.2 ⟨φ i, Finset.mem_image_of_mem φ (Finset.mem_univ i)⟩
    have hg : Function.Injective g := by
      intro i j h
      have := (S.1.equivFinOfCardEq S.2).injective h
      exact hφ (congrArg Subtype.val this)
    refine ⟨(S, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)),
      Finset.mem_univ _, ?_⟩
    funext i
    simp [subsetCols, g, S]
  · intro x _
    rfl

end Elem

open Elem in

theorem PlueckerCauchyBinet.intersectionNumber_baseChange : PlueckerCauchyBinet.Statement := by
  intro p q Z
  set A := Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) Z with hAdef
  have hA : 1 + Z * Z.conjTranspose = A * A.conjTranspose := by
    rw [hAdef, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp
  rw [hA, cauchyBinet, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hB : A.conjTranspose.submatrix (subsetCols S) id =
      (A.submatrix id (subsetCols S)).conjTranspose := by
    ext i j; simp
  rw [hB, det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem PlueckerHadamard.intersectionNumber_baseChange : PlueckerHadamard.Statement := by
  intro p q Z hZ
  set H := 1 + Z * Z.conjTranspose with hHdef
  have hpsd : H.PosSemidef := Matrix.PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)
  have hH : H.IsHermitian := hpsd.isHermitian
  set ev := hH.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := hpsd.eigenvalues_nonneg
  have hdet : H.det = ((∏ i, ev i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]; push_cast; rfl
  have htrH : H.trace = ((p * (1 + q) : ℝ) : ℂ) := by
    have hZZ : (Z * Z.conjTranspose).trace = ((p * q : ℕ) : ℂ) := by
      simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
      have : ∀ i j, Z i j * (starRingEnd ℂ) (Z i j) = 1 := by
        intro i j
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hZ i j]
        simp
      simp [this]
    rw [hHdef, trace_add, trace_one, hZZ]
    push_cast
    simp
    ring
  have hsum : ∑ i, ev i = p * (1 + q) := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [htrH] at h1
    have : ((∑ i, ev i : ℝ) : ℂ) = ((p * (1 + q) : ℝ) : ℂ) := by
      rw [h1]; push_cast; rfl
    exact_mod_cast this
  rw [hdet, Complex.ofReal_re]
  push_cast
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hamgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (fun _ : Fin p => 1 / (p : ℝ)) ev (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => hev i)
    have hrhs : ∑ i, 1 / (p : ℝ) * ev i = 1 + q := by
      rw [← Finset.mul_sum, hsum]; field_simp
    rw [hrhs] at hamgm
    have hprod : ∏ i, ev i = (∏ i, ev i ^ (1 / (p : ℝ))) ^ p := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hev i), one_div_mul_cancel hp'.ne', Real.rpow_one]
    rw [hprod]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hev i) _) hamgm p

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

def RestInnerTsumBound.Statement : Prop :=
  ∀ (p : ℝ) (k : ℕ) (c : ℕ → ℝ) (M : ℝ), 2 ≤ p → 1 ≤ k → (∀ n, |c n| ≤ M) →
    Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) ∧
      |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n| ≤ M * (2 * (p ^ k)⁻¹)

def RestKSumBound.Statement : Prop :=
  ∀ (p X : ℝ) (N : ℕ), 0 < p → 0 ≤ X → X ≤ 3 / 8 * p →
    ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) ≤ 1.5 * X / p ^ 2

def RestPrimeBoundOfFactor.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      (∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)) →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

def RestBoundOfPrimeBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)) (s : ℕ → ℕ → Fin f → Fin f)
      (e : ℕ → ℕ → Fin f → ℕ → ℚ),
    (∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|) →
    ∀ P : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
        |restPrimeModel f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Q s e p| ≤
        1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

end

end RestTerms

end GroundTheory.Heights₂.Heights
end


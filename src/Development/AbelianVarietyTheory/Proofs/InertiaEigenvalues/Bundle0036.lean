import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotXPowSuccDvdDetOfFirstOrderKernelEqZero
section
open Polynomial

namespace GlobalTheory

theorem exists_det_one_mul_mul_eq_diagonal {K : Type} [Field K] {a : ℕ}
    (A : Matrix (Fin a) (Fin a) K) :
    ∃ (P Q : Matrix (Fin a) (Fin a) K) (D : Fin a → K),
      P.det = 1 ∧ Q.det = 1 ∧ P * A * Q = Matrix.diagonal D := by
  obtain ⟨L, L', D, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A
  exact ⟨_, _, D, Matrix.TransvectionStruct.det_toMatrix_prod L,
    Matrix.TransvectionStruct.det_toMatrix_prod L', h⟩

theorem not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero :
    ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  classical
  intro K _ a m Ψ hker hm hdvd
  set A := Ψ.map fun p => p.coeff 0 with hA
  set B := Ψ.map fun p => p.coeff 1 with hB
  have hker' : ∀ x0 x1 : Fin a → K, A.mulVec x0 = 0 → B.mulVec x0 + A.mulVec x1 = 0 → x0 = 0 := by
    intro x0 x1 h0 h1
    by_contra hne
    refine hker (fun _ => x0) (fun _ => x1) (fun _ => ⟨h0, h1⟩) ?_
    exact (linearIndependent_unique_iff (v := fun _ : Fin 1 => x0)).2 hne
  obtain ⟨P, Q, D, hP, hQ, hD⟩ := exists_det_one_mul_mul_eq_diagonal A
  have hPu : IsUnit P.det := hP ▸ isUnit_one
  have hQu : IsUnit Q.det := hQ ▸ isUnit_one
  have hPinj : ∀ v : Fin a → K, P.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hPu.ne_zero hv
  have hQinj : ∀ v : Fin a → K, Q.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hQu.ne_zero hv

  have hcard : (Finset.univ.filter fun i => D i = 0).card ≤ m := by
    have h1 : A.rank = Fintype.card {i // D i ≠ 0} := by
      rw [← Matrix.rank_diagonal, ← hD, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu]
    have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h3 : Fintype.card {i // D i ≠ 0} = a - Fintype.card {i // D i = 0} := by
      rw [Fintype.card_subtype_compl]; simp
    have h4 : Fintype.card {i // D i = 0} = (Finset.univ.filter fun i => D i = 0).card :=
      Fintype.card_subtype _
    have h5 : Fintype.card {i // D i = 0} ≤ a := by
      simpa using Fintype.card_subtype_le (fun i => D i = 0)
    rw [Matrix.rank] at h1
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  have hAQ : ∀ v : Fin a → K, P.mulVec (A.mulVec (Q.mulVec v)) = fun i => D i * v i := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    ext i
    rw [Matrix.mulVec_diagonal]
  have hcol : ∀ i j, D j = 0 → (A * Q) i j = 0 := by
    intro i j hj
    have h1 : A.mulVec (Q.mulVec (Pi.single j 1)) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : k = j
      · subst hk; simp [hj]
      · simp [hk]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
    exact congrFun h1 i
  set Θ : Matrix (Fin a) (Fin a) K[X] := Ψ * Q.map C with hΘ
  have hΘ0 : ∀ i j, (Θ i j).coeff 0 = (A * Q) i j := by
    intro i j
    simp [hΘ, hA, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  have hΘ1 : ∀ i j, (Θ i j).coeff 1 = (B * Q) i j := by
    intro i j
    simp [hΘ, hB, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  set Θ' : Matrix (Fin a) (Fin a) K[X] :=
    Matrix.of fun i j => if D j = 0 then (Θ i j).divX else Θ i j with hΘ'
  have hfac : Θ = Θ' * Matrix.diagonal fun j => if D j = 0 then (X : K[X]) else 1 := by
    ext1 i j
    rw [Matrix.mul_diagonal]
    by_cases hj : D j = 0
    · have := Polynomial.divX_mul_X_add (Θ i j)
      rw [hΘ0, hcol i j hj] at this
      simpa [hΘ', hj] using this.symm
    · simp [hΘ', hj]
  have hdetΘ : Θ.det = Ψ.det := by
    have : (Q.map C).det = (1 : K[X]) := by
      have := RingHom.map_det (C : K →+* K[X]) Q
      rw [hQ, map_one] at this
      exact this.symm
    rw [hΘ, Matrix.det_mul, this, mul_one]
  have hdet : Ψ.det = Θ'.det * X ^ (Finset.univ.filter fun i => D i = 0).card := by
    rw [← hdetΘ]
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite]
    simp
  set T : Matrix (Fin a) (Fin a) K := Θ'.map fun p => p.coeff 0 with hT
  have hTinj : ∀ y : Fin a → K, T.mulVec y = 0 → y = 0 := by
    intro y hy
    set y0 : Fin a → K := fun j => if D j = 0 then y j else 0 with hy0
    set y1 : Fin a → K := fun j => if D j = 0 then 0 else y j with hy1
    have e0 : A.mulVec (Q.mulVec y0) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : D k = 0 <;> simp [hy0, hk]
    have e1 : B.mulVec (Q.mulVec y0) + A.mulVec (Q.mulVec y1) = 0 := by
      rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      ext i
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : D j = 0
      · simp [hT, hΘ', hy0, hy1, hj, Polynomial.coeff_divX, hΘ1]
      · simp [hT, hΘ', hy0, hy1, hj, hΘ0]
    have z0 : y0 = 0 := hQinj _ (hker' _ _ e0 e1)
    rw [z0, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add] at e1
    have z1 := hAQ y1
    rw [e1, Matrix.mulVec_zero] at z1
    ext k
    by_cases hk : D k = 0
    · simpa [hy0, hk] using congrFun z0 k
    · simpa [hy1, hk] using (congrFun z1 k).symm
  have hTdet : T.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hv (hTinj v hv0)
  apply hTdet
  have hc : T.det = Θ'.det.coeff 0 := by
    have := RingHom.map_det (Polynomial.constantCoeff : K[X] →+* K) Θ'
    exact this.symm
  rw [hc, ← Polynomial.X_dvd_iff]
  set ν := (Finset.univ.filter fun i => D i = 0).card
  have h1 : (X : K[X]) * X ^ ν ∣ Θ'.det * X ^ ν := by
    rw [← hdet, ← pow_succ']
    exact (pow_dvd_pow _ (by omega)).trans hdvd
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ Polynomial.X_ne_zero)).1 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXPowPrimePowSubOneMemSpan
section
namespace GlobalTheory

theorem sq_dvd_choose_prime_pow (l : ℕ) (hl : l.Prime) (b k : ℕ) (hb : 1 ≤ b) (hk0 : k ≠ 0)
    (hk : k < l ^ (b - 1)) : l ^ 2 ∣ (l ^ b).choose k := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨m, hm⟩ : ∃ m, l ^ b = m + 1 := Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'
  have hkb : j + 1 ≤ l ^ b := le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))
  have hC : (l ^ b).choose (j + 1) ≠ 0 := (Nat.choose_pos hkb).ne'

  have hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1) := by
    rw [hm]; exact Nat.add_one_mul_choose_eq m j

  have hv : padicValNat l (j + 1) < b - 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : l ^ padicValNat l (j + 1) ≤ j + 1 :=
      Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd
    have h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1) := Nat.pow_le_pow_right hl.pos hcon
    omega
  have hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1) := by
    rw [← hid]; exact dvd_mul_right _ _
  have hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0 := mul_ne_zero hC (Nat.succ_ne_zero j)
  rw [padicValNat_dvd_iff_le hne, padicValNat.mul hC (by omega : j + 1 ≠ 0)] at hdiv
  exact (padicValNat_dvd_iff_le hC).mpr (by omega)

theorem one_add_X_pow_prime_pow_sub_one_mem_span (l : ℕ) [Fact l.Prime] (b : ℕ) (hb : 1 ≤ b) :
    ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) ∈
      Ideal.span {((l : Polynomial ℤ)) ^ 2, Polynomial.X ^ (l ^ (b - 1))} := by

  have key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) =
      ∑ i ∈ Finset.range (l ^ b),
        Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i + 1 < l ^ (b - 1)
  ·
    obtain ⟨c, hc⟩ := sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  ·
    push_neg at hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneSubSumLeProdOneSubRange
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem one_sub_sum_le_prod_one_sub_range (x : ℕ → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (r : ℕ) : 1 - ∑ i ∈ Finset.range r, x i ≤ ∏ i ∈ Finset.range r, (1 - x i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n]
    have := mul_le_mul_of_nonneg_right ih hx1
    nlinarith [h0 n]

theorem sum_rpow_sub_le (q : ℝ) (r : ℕ) (σ : ℝ) (hq : 2 ≤ q) (hσ : (r : ℝ) + 5 / 2 ≤ σ) :
    ∑ i ∈ Finset.range r, q ^ ((i : ℝ) - σ) ≤ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i : ℕ, q ^ ((i : ℝ) - σ) = q ^ i / q ^ σ := by
    intro i; rw [Real.rpow_sub hq0, Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.sum_div, geom_sum_eq (by linarith : q ≠ 1)]
  have hqs : 0 < q ^ σ := Real.rpow_pos_of_pos hq0 σ
  have hrs : q ^ r / q ^ σ ≤ 1 / q ^ 2 := by
    have h1 : q ^ r / q ^ σ = q ^ ((r : ℝ) - σ) := by rw [Real.rpow_sub hq0, Real.rpow_natCast]
    have h2 : q ^ ((r : ℝ) - σ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hq0.le]; norm_num
    rw [h1]; linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpr : 0 < q ^ r := pow_pos hq0 r
  calc (q ^ r - 1) / (q - 1) / q ^ σ ≤ q ^ r / (q - 1) / q ^ σ := by
        gcongr; linarith
    _ = (q ^ r / q ^ σ) / (q - 1) := by ring
    _ ≤ (1 / q ^ 2) / (q - 1) := by gcongr
    _ ≤ 2 / q ^ 3 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hq0 2, pow_pos hq0 3]

theorem lattice_zeta_sq_bound : ∀ (q : ℝ) (r : ℕ) (σ : ℝ), 2 ≤ q → (r : ℝ) + 5 / 2 ≤ σ →
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 < 1 ∧
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 ≤ 16 * q ^ (-(3 : ℝ)) := by
  intro q r σ hq hσ
  have hq0 : 0 < q := by linarith
  set x : ℕ → ℝ := fun i => q ^ ((i : ℝ) - σ) with hx
  have hS := sum_rpow_sub_le q r σ hq hσ
  have hq3 : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q, mul_le_mul hq hq (by norm_num) hq0.le]
  set w : ℝ := 1 / q ^ 3 with hw
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq3
  have h0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos hq0 _).le

  have hD := one_sub_sum_le_prod_one_sub_range (fun i => min (x i) 1)
    (fun i => le_min (h0 i) zero_le_one) (fun i => min_le_right _ _) r
  have hmin : ∀ i ∈ Finset.range r, min (x i) 1 = x i := by
    intro i hi
    apply min_eq_left
    have : x i ≤ ∑ j ∈ Finset.range r, x j :=
      Finset.single_le_sum (fun j _ => h0 j) hi
    have : 2 / q ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  rw [Finset.sum_congr rfl hmin, Finset.prod_congr rfl (fun i hi => by rw [hmin i hi])] at hD
  set D := ∏ i ∈ Finset.range r, (1 - x i) with hDdef
  have h2w : 2 / q ^ 3 = 2 * w := by rw [hw]; ring
  have hDlow : 1 - 2 * w ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hP : ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹ = D⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hrhs : 16 * q ^ (-(3 : ℝ)) = 16 * w := by
    rw [Real.rpow_neg hq0.le, hw]; norm_num
  rw [hP, hrhs]
  have ha : 0 < 1 - 2 * w := by linarith
  have hPle : D⁻¹ ≤ (1 - 2 * w)⁻¹ := inv_anti₀ ha hDlow
  have hP0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hsq : D⁻¹ ^ 2 ≤ ((1 - 2 * w)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  have hkey : ((1 - 2 * w)⁻¹) ^ 2 ≤ 1 + 16 * w := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  have hkey2 : ((1 - 2 * w)⁻¹) ^ 2 < 2 := by
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemOfLe
section
namespace GlobalTheory.PowerScalarMembership

theorem pow_smul_mem_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
    (L : Submodule O V) (c : O) {x : V} {m n : ℕ} (hmn : m ≤ n) (h : c ^ m • x ∈ L) :
    c ^ n • x ∈ L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, mul_comm, mul_smul]
  exact L.smul_mem _ h

theorem exists_pow_smul_mem {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, c ^ m • x ∈ L := by
  have hx : x ∈ Submodule.span LL (L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨max m n, ?_⟩
    rw [smul_add]
    exact L.add_mem (pow_smul_mem_of_le L c (le_max_left _ _) hm)
      (pow_smul_mem_of_le L c (le_max_right _ _) hn)
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨k, b, hb⟩ := hc a
    refine ⟨k + m, ?_⟩
    have key : c ^ (k + m) • (a • y) = b • (c ^ m • y) := by
      rw [← algebraMap_smul LL (c ^ (k + m)), smul_smul, ← algebraMap_smul LL b,
        ← algebraMap_smul LL (c ^ m), smul_smul, hb, map_pow, map_pow, pow_add]
      congr 1
      ring
    rw [key]
    exact L.smul_mem b hm

theorem main : ∀ {LL O : Type} [inst : Field LL] [inst_1 : CommRing O] [inst_2 : Algebra O LL] [TopologicalSpace LL] {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module LL V] [inst_6 : Module O V] [IsScalarTower O LL V] (c : O), (∀ (a : LL), ∃ (k : ℕ) (b : O), (Algebra.algebraMap O LL : O → LL) b = (Algebra.algebraMap O LL : O → LL) c ^ k * a) → ∀ (L S : Submodule O V), Submodule.span LL (↑L : Set V) = ⊤ → Submodule.FG S → ∃ (m : ℕ), ∀ x ∈ S, c ^ m • x ∈ L := by
  intro LL O _ _ _ _ V _ _ _ _ c hc L S hL hS
  obtain ⟨s, rfl⟩ := hS
  choose f hf using fun x => exists_pow_smul_mem (LL := LL) c hc L hL x
  refine ⟨s.sup f, fun x hx => ?_⟩
  have hle : Submodule.span O (s : Set V) ≤ L.comap ((c ^ s.sup f) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    exact pow_smul_mem_of_le L c (Finset.le_sup hy) (hf y)
  simpa using hle hx

end GlobalTheory.PowerScalarMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubDvdChoosePrimePowOfLt
section
open scoped BigOperators

namespace GlobalTheory

theorem pow_sub_dvd_choose_prime_pow_of_lt :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  intro l a c i hl hi hlt
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : v ≤ c := by
    have h1 : l ^ v ≤ l ^ v * m := Nat.le_mul_of_pos_right _ hm0
    have h2 : l ^ v < l ^ (c + 1) := lt_of_le_of_lt h1 hlt
    have := (Nat.pow_lt_pow_iff_right hl.one_lt).1 h2
    omega
  have hpos : 0 < l ^ a := pow_pos hl.pos a
  have key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m) := by
    obtain ⟨n, hn⟩ : ∃ n, l ^ a = n + 1 := ⟨l ^ a - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1 := ⟨l ^ v * m - 1, by omega⟩
    rw [hn, hk]
    refine ⟨n.choose k, ?_⟩
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq n k).symm
  have h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m) := by
    rcases le_or_gt v a with h | h
    · have key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m)) := by
        rw [← pow_add, Nat.add_sub_of_le h, ← mul_assoc]
        exact key
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'
    · rw [show a - v = 0 by omega, pow_zero]
      exact one_dvd _
  have hcop : (l ^ (a - v)).Coprime m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m) := hcop.dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubOneLe
section
namespace GlobalTheory.UltrametricPowerBound

variable {l : ℕ} [Fact (Nat.Prime l)]

lemma ultra (q r : ℚ_[l]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean q r

lemma pow_sub_one_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ ‖w - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 = w * (w ^ k - 1) + (w - 1) := by ring
    rw [e]
    refine (ultra _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖w‖ * ‖w ^ k - 1‖ ≤ 1 * ‖w ^ k - 1‖ := by gcongr
      _ ≤ ‖w - 1‖ := by rw [one_mul]; exact ih

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (w : ℚ_[l]), ‖w‖ ≤ (1 : ℝ) → ∀ (k : ℕ),
    ‖w ^ k - (1 : ℚ_[l]) - (↑k : ℚ_[l]) * (w - (1 : ℚ_[l]))‖ ≤ ‖w - (1 : ℚ_[l])‖ ^ (2 : ℕ) := by
  intro l _ w hw k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℚ_[l]) * (w - 1)
        = (w ^ k - 1 - (k : ℚ_[l]) * (w - 1)) + (w - 1) * (w ^ k - 1) := by push_cast; ring
    rw [e]
    refine (ultra _ _).trans (max_le ih ?_)
    rw [norm_mul, sq]
    exact mul_le_mul_of_nonneg_left (pow_sub_one_le w hw k) (norm_nonneg _)

end GlobalTheory.UltrametricPowerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnity
section
namespace GlobalTheory

open PowerSeries in

theorem powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  classical
  obtain ⟨z, rfl⟩ : X ∣ y := by rwa [PowerSeries.X_dvd_iff]
  have hs : HasSubst (X * z) := HasSubst.of_constantCoeff_zero' hy
  have hu1 : coeff 1 (X * z) = constantCoeff z := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [hu1] at hu

  have hc : ∀ n, coeff n (a.subst (X * z)) =
      ∑ d ∈ Finset.range (n + 1), coeff d a * coeff (n - d) (z ^ d) := by
    intro n
    rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)),
        smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

  have main : ∀ k, 0 < k → coeff k a = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have h1 := hc k
      rw [ha, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, map_pow] at h1
      · have h2 : coeff k a * (1 - constantCoeff z ^ k) = 0 := by
          rw [mul_sub, mul_one, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm (hu k hk)
      · intro d hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [coeff_one, hk.ne']
        · rw [ih d (Finset.mem_range.mp hd) hd0, zero_mul]
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_C, if_neg (Nat.succ_ne_zero n)]
    exact main (n + 1) (Nat.succ_pos n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRing
section
namespace GlobalTheory

theorem projective_compHom_of_free_of_finite_free :
    ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  intro Z S A D _ _ _ _ _ z a N q x hN hli ⟨d, w, hw⟩
  letI : Module Z N := Module.compHom _ (a.comp z)
  have hsm : ∀ (r : Z) (n : N), ((r • n : N) : D) = a (z r) • (n : D) := fun _ _ => rfl
  let f : (Fin q → Fin d → Z) →ₗ[Z] N :=
    { toFun := fun c => ⟨∑ i, a (∑ m, z (c i m) * w m) • x i, (hN _).2 ⟨_, rfl⟩⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        simp [add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul, mul_assoc, ← Finset.mul_sum] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 := hli (fun i => ∑ m, z (c i m) * w m) (congrArg Subtype.val hc)
    funext i
    have h2 : (0 : S) = ∑ m, z (c i m) * w m := (congrFun h1 i).symm
    exact (hw 0).unique h2 (by simp)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := (hN y).1 hy
    choose c hc _ using fun i => hw (s i)
    refine ⟨c, Subtype.ext ?_⟩
    change ∑ i, a (∑ m, z (c i m) * w m) • x i = ∑ i, a (s i) • x i
    exact Finset.sum_congr rfl fun i _ => by rw [← hc i]
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end GlobalTheory
end


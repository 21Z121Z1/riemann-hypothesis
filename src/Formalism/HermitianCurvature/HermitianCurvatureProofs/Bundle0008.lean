import Formalism.HermitianCurvature.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0006
import Formalism.HermitianCurvature.Bundle0001
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal
section
namespace Formalism.FourierDecayAlt.P.K

open Matrix Finset Real Formalism.FourierDecayAlt.K

variable {K : Type} [Field K] {n : ℕ}

theorem diag_mul {a b : Matrix (Fin n) (Fin n) K} (ha : a.BlockTriangular id)
    (hb : b.BlockTriangular id) (i : Fin n) : (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem upUni_mul {a b : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) (hb : IsUpUni b) :
    IsUpUni (a * b) := ⟨Matrix.BlockTriangular.mul ha.1 hb.1, fun i => by rw [diag_mul ha.1 hb.1, ha.2, hb.2, one_mul]⟩

theorem upUni_det {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : a.det = 1 := by
  rw [Matrix.det_of_upperTriangular ha.1]
  simp [ha.2]

theorem upUni_isUnit {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUnit a.det := by
  rw [upUni_det ha]
  exact isUnit_one

theorem upUni_inv {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUpUni a⁻¹ := by
  haveI := Matrix.invertibleOfIsUnitDet a (upUni_isUnit ha)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular ha.1
  refine ⟨hinv, fun i => ?_⟩
  have h := diag_mul hinv ha.1 i
  rw [Matrix.nonsing_inv_mul _ (upUni_isUnit ha), ha.2, mul_one, Matrix.one_apply_eq] at h
  exact h.symm

theorem antidiag_mul_diagonal (d : Fin n → K) :
    w0 n * diagonal d = Matrix.of fun i j => if i = Fin.rev j then d j else 0 := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [w0, Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ i = Fin.rev j := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  by_cases h : i = Fin.rev j
  · rw [if_pos (hiff.mpr h), if_pos h, one_mul]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, zero_mul]

theorem mulW_apply (a : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    (a * (w0 n * diagonal d) : Matrix (Fin n) (Fin n) K) i j = a i (Fin.rev j) * d j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Wmul_apply (c : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    ((w0 n * diagonal d) * c : Matrix (Fin n) (Fin n) K) i j = d (Fin.rev i) * c (Fin.rev i) j := by
  rw [antidiag_mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro k _ hk
    simp only [Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h
    apply hk
    rw [h, Fin.rev_rev]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lower_eq_one {a c : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (ha : IsUpUni a)
    (hc : IsUpUni c) (hd : ∀ x, d x ≠ 0)
    (h : a * (w0 n * diagonal d) = (w0 n * diagonal d) * c) : a = 1 := by
  ext i k
  rw [Matrix.one_apply]
  split_ifs with hik
  · subst hik
    exact ha.2 i
  · rcases lt_or_gt_of_ne hik with h' | h'
    · have e := congrFun (congrFun h i) (Fin.rev k)
      rw [mulW_apply, Wmul_apply, Fin.rev_rev] at e
      have hc0 : c (Fin.rev i) (Fin.rev k) = 0 := hc.1 (Fin.rev_lt_rev.mpr h')
      rw [hc0, mul_zero] at e
      exact (mul_eq_zero.mp e).resolve_right (hd _)
    · exact ha.1 h'

theorem right_eq_one {b : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (hd : ∀ x, d x ≠ 0)
    (h : (w0 n * diagonal d) * b = w0 n * diagonal d) : b = 1 := by
  ext x j
  have e := congrFun (congrFun h (Fin.rev x)) j
  have e1 : (w0 n * Matrix.diagonal d : Matrix (Fin n) (Fin n) K) (Fin.rev x) j =
      ((w0 n * Matrix.diagonal d) * 1 : Matrix (Fin n) (Fin n) K) (Fin.rev x) j := by
    rw [Matrix.mul_one]
  rw [e1, Wmul_apply, Wmul_apply, Fin.rev_rev] at e
  exact mul_left_cancel₀ (hd x) e

theorem bigCellFree : BigCellFree := by
  intro K' _ m v v' u u' d hv hv' hu hu' hd h
  have hvU := upUni_isUnit hv
  have hv'U := upUni_isUnit hv'
  rw [Matrix.mul_assoc v (w0 m) (Matrix.diagonal d)] at h
  obtain ⟨W, hW⟩ : ∃ W, W = w0 m * Matrix.diagonal d := ⟨_, rfl⟩
  rw [← hW] at h
  have ha : IsUpUni (v⁻¹ * u * v) := upUni_mul (upUni_mul (upUni_inv hv) hu) hv
  have hc : IsUpUni (v' * u' * v'⁻¹) := upUni_mul (upUni_mul hv' hu') (upUni_inv hv')
  have hcU := upUni_isUnit hc
  have key : (v⁻¹ * u * v) * W * (v' * u' * v'⁻¹) = W := by
    have e : v⁻¹ * (u * (v * W * v') * u') * v'⁻¹ = W := by
      rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hvU, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hv'U, Matrix.mul_one]
    rw [show (v⁻¹ * u * v) * W * (v' * u' * v'⁻¹) = v⁻¹ * (u * (v * W * v') * u') * v'⁻¹ by
      simp only [Matrix.mul_assoc]]
    exact e
  have key2 : (v⁻¹ * u * v) * W = W * (v' * u' * v'⁻¹)⁻¹ := by
    calc (v⁻¹ * u * v) * W
        = (v⁻¹ * u * v) * W * ((v' * u' * v'⁻¹) * (v' * u' * v'⁻¹)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hcU, Matrix.mul_one]
      _ = ((v⁻¹ * u * v) * W * (v' * u' * v'⁻¹)) * (v' * u' * v'⁻¹)⁻¹ :=
          (Matrix.mul_assoc _ _ _).symm
      _ = W * (v' * u' * v'⁻¹)⁻¹ := by rw [key]
  have ha1 : v⁻¹ * u * v = 1 := lower_eq_one ha (upUni_inv hc) hd (by rw [← hW]; exact key2)
  rw [ha1, Matrix.one_mul] at key
  have hc1 : v' * u' * v'⁻¹ = 1 := right_eq_one hd (by rw [← hW]; exact key)
  constructor
  · calc u = v * (v⁻¹ * u * v) * v⁻¹ := by
          simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hvU, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hvU, Matrix.mul_one]
      _ = 1 := by rw [ha1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hvU]
  · calc u' = v'⁻¹ * (v' * u' * v'⁻¹) * v' := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hv'U, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hv'U, Matrix.mul_one]
      _ = 1 := by rw [hc1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hv'U]

theorem jointTheoremA : JointTheoremA := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.coarseBound
  refine ⟨2 * C₀, C, ?_⟩
  intro Kx Θ f r e σ hKx hf hΘ hr he hσ hrec
  have hΘ1 : 1 ≤ Θ := by linarith
  have hΘpos : 0 < Θ := by linarith
  have ha0 : 0 ≤ C₀ / Θ := div_nonneg (by linarith) hΘpos.le
  have hq : C₀ / Θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hΘpos]
    linarith
  have ha : (C₀ / Θ) ^ f ≤ 1 / 2 := by
    calc (C₀ / Θ) ^ f ≤ (C₀ / Θ) ^ 1 := pow_le_pow_of_le_one ha0 (by linarith) hf
      _ ≤ 1 / 2 := by rw [pow_one]; exact hq
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  have hε0 : 0 ≤ C₀ * Θ ^ (-(Kx - 5 / 2)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hΘpos.le _)
  have hεa : (C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (C₀ / Θ) ^ f := by
    apply pow_le_pow_left₀ hε0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrp (by linarith)
  exact hC r ((C₀ / Θ) ^ f) ((C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f) e σ (pow_nonneg ha0 _) ha
    (pow_nonneg hε0 _) hεa hr he hσ hrec

end Formalism.FourierDecayAlt.P.K

theorem Formalism.FourierDecayAlt.P.big_cell_free : Formalism.FourierDecayAlt.K.BigCellFree := Formalism.FourierDecayAlt.P.K.bigCellFree

theorem Formalism.FourierDecayAlt.P.joint_theorem_A' : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BoxOne
section
namespace Formalism.FourierDecayAlt.P.BoxOne

open NumberField Finset

theorem geom_prod_sum_le {ι : Type} [Fintype ι] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, q ^ (k i) ≤ (1 / (1 - q)) ^ Fintype.card ι := by
  classical
  set M := T.sup (fun k => Finset.univ.sup k) + 1 with hM
  have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := k) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun k => Finset.univ.sup k) hk)
  have hgeom : ∑ n ∈ Finset.range M, q ^ n ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := M) hq0 hq1
    rwa [← Finset.range_eq_Ico, pow_zero] at h
  calc ∑ k ∈ T, ∏ i, q ^ (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ i, q ^ (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun i _ => pow_nonneg hq0 _)
    _ = ∏ i : ι, ∑ n ∈ Finset.range M, q ^ n := by
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, (1 / (1 - q)) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun n _ => pow_nonneg hq0 n)
          (fun _ _ => hgeom)
    _ = (1 / (1 - q)) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

variable {E : Type} [Field E] [NumberField E]

theorem term_le (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (Kx : ℝ) (hK : 0 ≤ Kx) (l : E)
    (hl0 : l ≠ 0) :
    ∏ w, min 1 ((x w / w l) ^ Kx) ≤ ∏ w, ((1 / 2 : ℝ) ^ Kx) ^ (Nat.log 2 ⌊w l / x w⌋₊) := by
  apply Finset.prod_le_prod (fun w _ => le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg (hx w).le (by positivity)) _))
  intro w _
  have hpos : 0 < x w / w l := div_pos (hx w) (InfinitePlace.pos_iff.2 hl0)
  rw [Formalism.SA.P.min_one_rpow _ _ hpos hK, ← Formalism.SA.P.pow_rpow_comm (1 / 2 : ℝ) Kx (by norm_num)]
  apply Real.rpow_le_rpow (le_min zero_le_one hpos.le) _ hK
  have hu : 0 < w l / x w := div_pos (InfinitePlace.pos_iff.2 hl0) (hx w)
  have := Formalism.SA.P.min_one_inv_le (w l / x w) hu
  rwa [one_div_div] at this

end Formalism.FourierDecayAlt.P.BoxOne

namespace Formalism.FourierDecayAlt.P

open NumberField Finset

theorem box_weights_sum_to_one : Formalism.FourierDecayAlt.BoxSumOne := by
  intro Kx hKx
  set p : ℝ := (1 / 2 : ℝ) ^ Kx with hp
  set q : ℝ := 4 * p with hq
  have hp0 : 0 < p := by rw [hp]; positivity
  have hp1 : p < 1 / 4 := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hKx
    rw [show ((1 / 2 : ℝ) ^ (2 : ℝ)) = 1 / 4 by rw [Real.rpow_two]; norm_num] at h
    exact h
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  refine ⟨400 * (1 / (1 - q)), ?_⟩
  intro E _ _ _ b hb x hx hX S hS
  classical
  set f := Fintype.card (InfinitePlace E) with hf
  set N : ℝ := (FractionalIdeal.absNorm b : ℝ) with hN
  have hNpos : 0 < N := Formalism.SA.P.absNorm_pos b hb
  set X := ∏ w, x w with hXdef
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun w _ => (hx w).le
  have hX2 : X ^ 2 ≤ N := by
    calc X ^ 2 ≤ (√N) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ = N := Real.sq_sqrt hNpos.le
  let kv : E → InfinitePlace E → ℕ := fun l w => Nat.log 2 ⌊w l / x w⌋₊
  have hfib : ∀ k ∈ S.image kv, ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
      (400 : ℝ) ^ f * ∏ w, q ^ (k w) := by
    intro k _
    set B := ∏ w, p ^ (k w) with hB
    have hB0 : 0 ≤ B := Finset.prod_nonneg fun w _ => pow_nonneg hp0.le _
    have hterm : ∀ l ∈ S.filter (fun l => kv l = k), ∏ w, min 1 ((x w / w l) ^ Kx) ≤ B := by
      intro l hl
      rw [Finset.mem_filter] at hl
      obtain ⟨hlS, hlk⟩ := hl
      rw [hB, ← hlk]
      exact Formalism.FourierDecayAlt.P.BoxOne.term_le x hx Kx (by linarith) l (hS l hlS).2
    have hcard : (((S.filter (fun l => kv l = k)).card : ℕ) : ℝ) ≤
        (100 : ℝ) ^ f * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / N := by
      apply Formalism.SA.P.card_box_le b hb (fun w => 2 ^ (k w + 1) * x w)
        (fun w => by have := hx w; positivity)
      intro l hl
      rw [Finset.mem_filter] at hl
      obtain ⟨hlS, hlk⟩ := hl
      refine ⟨(hS l hlS).1, (hS l hlS).2, fun w => ?_⟩
      have := Formalism.SA.P.nat_log_floor_upper (w l / x w) (div_nonneg (by positivity) (hx w).le)
      rw [div_lt_iff₀ (hx w)] at this
      rw [← hlk]; exact this
    have hpt : ∀ w, (2 ^ (k w + 1) * x w) ^ 2 * p ^ (k w) = 4 * x w ^ 2 * q ^ (k w) := by
      intro w
      rw [hq, mul_pow (4 : ℝ) p (k w), show (4 : ℝ) ^ (k w) = (2 ^ (k w)) ^ 2 by rw [sq, ← mul_pow]; norm_num]
      ring
    have hid : (∏ w, (2 ^ (k w + 1) * x w) ^ 2) * B = 4 ^ f * X ^ 2 * ∏ w, q ^ (k w) := by
      rw [hB, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun w _ => hpt w),
        Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← hf, Finset.prod_pow]
    have hQ0 : 0 ≤ ∏ w, q ^ (k w) := Finset.prod_nonneg fun w _ => pow_nonneg hq0 _
    calc ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx)
        ≤ (S.filter (fun l => kv l = k)).card • B := Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((S.filter (fun l => kv l = k)).card : ℝ) * B := by rw [nsmul_eq_mul]
      _ ≤ (100 : ℝ) ^ f * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / N * B :=
          mul_le_mul_of_nonneg_right hcard hB0
      _ = (100 : ℝ) ^ f * 4 ^ f * (∏ w, q ^ (k w)) * (X ^ 2 / N) := by
          rw [div_mul_eq_mul_div, mul_assoc, hid]; ring
      _ ≤ (100 : ℝ) ^ f * 4 ^ f * (∏ w, q ^ (k w)) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hNpos).2 hX2) (by positivity)
      _ = (400 : ℝ) ^ f * ∏ w, q ^ (k w) := by
          rw [show (400 : ℝ) ^ f = 100 ^ f * 4 ^ f by rw [← mul_pow]; norm_num]; ring
  rw [← Finset.sum_fiberwise_of_maps_to (g := kv) (t := S.image kv)
    (fun l hl => Finset.mem_image_of_mem kv hl)]
  calc ∑ k ∈ S.image kv, ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx)
      ≤ ∑ k ∈ S.image kv, (400 : ℝ) ^ f * ∏ w, q ^ (k w) := Finset.sum_le_sum hfib
    _ = (400 : ℝ) ^ f * ∑ k ∈ S.image kv, ∏ w, q ^ (k w) := by rw [Finset.mul_sum]
    _ ≤ (400 : ℝ) ^ f * (1 / (1 - q)) ^ f :=
        mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.BoxOne.geom_prod_sum_le q hq0 hq1 _) (by positivity)
    _ = (400 * (1 / (1 - q))) ^ f := by rw [mul_pow]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FacSuccOfNotMem
section
namespace Formalism.FourierDecayAlt.P.Fejer

open Real Finset Formalism.FourierDecayAlt.P.Herglotz

variable {d : ℕ}

lemma fac_succ_of_mem (N : ℕ) (t : ℤ) (ht : t ∈ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 1 - |((t : ℤ) : ℝ)| / ((N : ℝ) + 1) := by
  rw [Finset.mem_Icc] at ht
  have habs : |t| ≤ (N : ℤ) := abs_le.2 ht
  have hz : (0 : ℤ) ≤ ((N + 1 : ℕ) : ℤ) - |t| := by push_cast; omega
  have hN0 : ((N : ℝ) + 1) ≠ 0 := by positivity
  unfold fac
  rw [show (((((N + 1 : ℕ) : ℤ) - |t|).toNat : ℕ) : ℝ)
      = ((((((N + 1 : ℕ) : ℤ) - |t|).toNat : ℕ) : ℤ) : ℝ) by norm_cast,
    Int.toNat_of_nonneg hz]
  push_cast
  field_simp

lemma fac_succ_of_not_mem (N : ℕ) (t : ℤ) (ht : t ∉ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 0 := by
  rw [Finset.mem_Icc] at ht
  have habs : (N : ℤ) < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  have hz : (((N + 1 : ℕ) : ℤ) - |t|).toNat = 0 := by
    rw [Int.toNat_eq_zero]; push_cast; omega
  unfold fac
  rw [hz]; simp

lemma wt_succ_of_mem (N : ℕ) (τ : Fin d → ℤ)
    (hτ : τ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)) :
    wt (N + 1) τ = ∏ j, (1 - |((τ j : ℤ) : ℝ)| / ((N : ℝ) + 1)) := by
  rw [Fintype.mem_piFinset] at hτ
  unfold wt
  exact Finset.prod_congr rfl (fun j _ => fac_succ_of_mem N (τ j) (hτ j))

lemma wt_succ_of_not_mem (N : ℕ) (τ : Fin d → ℤ)
    (hτ : τ ∉ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)) :
    wt (N + 1) τ = 0 := by
  rw [Fintype.mem_piFinset] at hτ
  simp only [not_forall] at hτ
  obtain ⟨j, hj⟩ := hτ
  unfold wt
  exact Finset.prod_eq_zero (Finset.mem_univ j) (fac_succ_of_not_mem N (τ j) hj)

end Formalism.FourierDecayAlt.P.Fejer

namespace Formalism.FourierDecayAlt.P

open Real Finset Formalism.FourierDecayAlt.P.Herglotz Formalism.FourierDecayAlt.P.Fejer

theorem herglotz_fejer_Zd : Formalism.FourierDecayAlt.H.HerglotzFejerZd := by
  intro d A hPD N x
  have h := hPD (box d (N + 1)) (ee x)
  simp_rw [mul_assoc, ee_mul_conj] at h
  have hd := dsum (fun τ => A τ * ee x τ) (box d (N + 1))
  beta_reduce at hd
  rw [hd] at h
  have hN0 : N + 1 ≠ 0 := by omega
  have heq : (∑' τ, ((wt (N + 1) τ : ℝ) : ℂ) * (A τ * ee x τ)) =
      (((((N + 1 : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) *
        ∑' τ, (((box d (N + 1) ×ˢ box d (N + 1)).filter (fun p => p.1 - p.2 = τ)).card : ℂ) *
          (A τ * ee x τ) := by
    rw [← tsum_mul_left]
    congr 1
    funext τ
    rw [← wt_eq (N + 1) hN0 τ]
    push_cast
    ring
  have hfin : (∑' τ, ((wt (N + 1) τ : ℝ) : ℂ) * (A τ * ee x τ)) =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N),
        (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
          Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ)) := by
    rw [tsum_eq_sum (s := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N))]
    · refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [wt_succ_of_mem N σ hσ, mul_assoc]
      rfl
    · intro τ hτ
      rw [wt_succ_of_not_mem N τ hτ]
      simp
  rw [← hfin, heq, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) h

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FderivDecomp
section
open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

theorem clm_decomp (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (1 / 2 : ℂ) * (L 1 - I * L I) * v + (1 / 2 : ℂ) * (L 1 + I * L I) * (starRingEnd ℂ v) := by

  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, v = x + y * I := ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
  have e : (x : ℂ) + y * I = x • (1 : ℂ) + y • I := by rw [Complex.real_smul, Complex.real_smul, mul_one]
  have hL : L ((x : ℂ) + y * I) = (x : ℂ) * L 1 + (y : ℂ) * L I := by
    rw [e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((y : ℂ) * L I) * Complex.I_sq

theorem fderiv_decomp (f : ℂ → ℂ) (ζ v : ℂ) :
    fderiv ℝ f ζ v = wZ f ζ * v + wZb f ζ * (starRingEnd ℂ v) := by
  unfold wZ wZb
  exact clm_decomp _ v

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    | simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by

  intro w1 h1 w2 h2 a b ha hb hab
  simp only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢
  have hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re := by simp
  rw [hre]
  rcases le_total w1.re w2.re with h | h
  · calc TT < Real.exp w1.re ^ 2 := h1
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re) := by
          rw [show a = 1 - b by linarith]; ring
        have : w1.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
        gcongr
  · calc TT < Real.exp w2.re ^ 2 := h2
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re) := by
          rw [show b = 1 - a by linarith]; ring
        have : w2.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]
        gcongr

theorem Hh_add_period (TT : ℝ) (w : ℂ) (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by

  simp only [Hh, Set.mem_setOf_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end


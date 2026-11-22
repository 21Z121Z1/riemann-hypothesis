import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
section
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

theorem pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem pd_const (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp

theorem pd_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g i j) := by
  refine ⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_star_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_add]

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg b Q) :
    U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_mul]

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1

theorem pd_prod {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1

theorem pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2

end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

namespace Formalism.FourierDecayAlt.P

open PartialDerivativeAlgebra

theorem homogeneity_natural_degree : C6.SSNatHomog := by
  intro m m' E _ _ OO h1 h2 w w' Gv T T' th hGv hT hT' _ _
  simp only [C6.unitOf]
  rw [h1, h2, smul_smul, smul_smul]
  congr 1
  have hc : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr (mul_pos hT hT')
  have hab : Real.sqrt (T / Gv) * Real.sqrt (T' / Gv) = Real.sqrt (T * T') / Gv := by
    rw [← Real.sqrt_mul (div_nonneg hT.le hGv.le),
      show T / Gv * (T' / Gv) = (T * T') / (Gv * Gv) by ring,
      Real.sqrt_div' _ (mul_self_nonneg Gv), Real.sqrt_mul_self hGv.le]
  have hab' : ((Real.sqrt (T / Gv) : ℝ) : ℂ) * ((Real.sqrt (T' / Gv) : ℝ) : ℂ)
      = ((Real.sqrt (T * T') : ℝ) : ℂ) / (Gv : ℂ) := by
    rw [← Complex.ofReal_mul, hab, Complex.ofReal_div]
  have hc' : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hG' : (Gv : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hGv.ne'
  rw [mul_assoc, hab']
  field_simp

theorem polynomial_root_facts : C6.RootFacts := by
  intro s D' hs hD
  have hs0 : s ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp s hs0
  have hnd : (Polynomial.nthRoots s D').Nodup := hprim.nthRoots_nodup hD
  refine ⟨?_, ?_⟩
  · unfold G.rootSet
    rw [Multiset.toFinset_card_of_nodup hnd, hprim.card_nthRoots D']
    rw [if_pos (IsAlgClosed.exists_pow_nat_eq D' (by omega))]
  · intro z hz
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [← hz, norm_pow, one_div, Real.pow_rpow_inv_natCast (norm_nonneg z) hs0]

theorem gram_function_last_minor : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith

private theorem isPolyDeg_one_mulVec_apply {M : ℕ} (v : Fin M → ℂ) (j : Fin M) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin M) (Fin M) ℂ => Matrix.mulVec g v j) := by
  have h := pd_sum (N := M) (Finset.univ : Finset (Fin M))
    (P := fun m g => g j m * v m) (a := 1 + 0)
    (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))
  simpa [Matrix.mulVec, dotProduct] using h

theorem zhat_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => Zhat k r z z' g a b) := by
  have hH : ∀ i, U.IsPolyDeg 1
      (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) := by
    intro i
    have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
      (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1)
      (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))
    simpa [Matrix.mulVec, dotProduct] using h
  have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
    (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1)
    (fun i _ => pd_mul (pd_const _ 0) (hH i))
  simpa [Zhat, herm, dotProduct] using h

private theorem isPolyDeg_star' {M a : ℕ} {P : Matrix (Fin M) (Fin M) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · have hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree := by
      unfold totalDegree; exact Finset.sup_mono (support_map_subset _ _)
    exact (totalDegree_rename_le _ _).trans (hm.trans hq)
  · dsimp only
    rw [hP g, eval_rename, eval_map]
    change starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _
    rw [eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem zhat_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => star (Zhat k r z z' g a b)) := by
  exact isPolyDeg_star' (zhat_pd k r z z' a b)

theorem minor_polynomial_property : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)

theorem dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by
  exact isPolyDeg_star' (minor_polynomial_property k r z z' l)

theorem gram_function_polynomial : C6.GfPoly := by
  intro k r z z'
  have hL := pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1)))
    (dmin_star_pd k r z z' (Fin.last (r + 1)))
  have hR0 := pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩)
    (dmin_star_pd k r z z' ⟨r, by omega⟩)
  have hR := pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0
  have hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) *
      star (Dmin k r z z' g (Fin.last (r + 1)))) :=
    pd_mono (by simp; omega) hL
  have hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
      (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩))) :=
    pd_mono (by simp; omega) hR
  have h := pd_sub hL' hR'
  convert h using 2 with g
  simp only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerDensityThreshold
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

set_option maxHeartbeats 2000000 in
theorem inner_density_threshold : C6.DensThreshJ := by
  intro C₁ c₃ C₂ hC₁ hc₃
  set K : ℝ := 24 * C₁ + 192 * c₃ + 5 * (C₂ : ℝ) + 80 with hK
  refine ⟨⌈K⌉₊, ?_⟩
  intro CV hCV r n s A hr hn hs hA
  have hKV : K ≤ (CV : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hCV)
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hsx : (s:ℝ) ≤ r := by exact_mod_cast hs
  have hy : (1:ℝ) ≤ n := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hA' : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) ≤ A := by
    unfold C6.AV at hA
    have e : (r:ℝ) * ((CV:ℝ) * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
        (CV:ℝ) * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) + (CV:ℝ) * ((r:ℝ) * n ^ 2) := by ring
    rw [e] at hA
    have : 0 ≤ (CV:ℝ) * ((r:ℝ) * n ^ 2) := by positivity
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) ≤ (CV:ℝ) * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_right hKV (by positivity)
    linarith
  have hs2 : (s:ℝ) ^ 2 ≤ (r:ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
  have h8 : 8 * (2 * (r:ℝ) + 1) ≤ 24 * r := by linarith
  have x35 : (r:ℝ) ^ 3 ≤ (r:ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
  have x15 : (r:ℝ) ≤ (r:ℝ) ^ 5 := by
    calc (r:ℝ) = (r:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hx (by norm_num)
  have x24 : (r:ℝ) ^ 2 * n ≤ (r:ℝ) ^ 4 * n :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx (by norm_num)) (by positivity)
  have hpos : (0:ℝ) < 8 * (2 * (r:ℝ) + 1) := by positivity

  have hb : 5 * (r:ℝ) * (((C₂ * s ^ 2 : ℕ) : ℝ) + 1) + 2 * (r:ℝ) * ((1 : ℕ) : ℝ) ≤
      (5 * (C₂:ℝ) + 7) * (r:ℝ) ^ 5 := by
    push_cast
    have : (C₂:ℝ) * (s:ℝ) ^ 2 ≤ (C₂:ℝ) * (r:ℝ) ^ 2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
    have e : 5 * (r:ℝ) * ((C₂:ℝ) * (r:ℝ) ^ 2 + 1) + 2 * (r:ℝ) = 5 * (C₂:ℝ) * (r:ℝ) ^ 3 + 7 * r := by ring
    have h3 : 5 * (r:ℝ) * ((C₂:ℝ) * (s:ℝ) ^ 2 + 1) ≤ 5 * (r:ℝ) * ((C₂:ℝ) * (r:ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 5 * (C₂:ℝ))
    nlinarith
  have key : ∀ X : ℝ, X * (8 * (2 * (r:ℝ) + 1)) + (5 * C₂ + 7) * (r:ℝ) ^ 5 ≤ A → X ≤ U.a1 r A (C₂ * s ^ 2) 1 := by
    intro X hX
    unfold U.a1
    rw [le_div_iff₀ hpos]
    linarith
  have hx5 : 0 ≤ (r:ℝ) ^ 5 := by positivity
  have hx4y : 0 ≤ (r:ℝ) ^ 4 * n := by positivity
  refine ⟨key _ ?_, key _ ?_, key _ ?_⟩
  · have a : C₁ * (s:ℝ) ^ 2 * (8 * (2 * (r:ℝ) + 1)) ≤ C₁ * (r:ℝ) ^ 2 * (24 * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs2 hC₁) h8 (by positivity) (by positivity)
    have e : C₁ * (r:ℝ) ^ 2 * (24 * r) = 24 * C₁ * (r:ℝ) ^ 3 := by ring
    have := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 24 * C₁)
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = K * ((r:ℝ) ^ 4 * n) + K * (r:ℝ) ^ 5 := by ring
    have : 0 ≤ K * ((r:ℝ) ^ 4 * n) := by positivity
    have : 0 ≤ 192 * c₃ * (r:ℝ) ^ 5 := by positivity
    have : K * (r:ℝ) ^ 5 = (24 * C₁ + 5 * C₂ + 7) * (r:ℝ) ^ 5 + 192 * c₃ * (r:ℝ) ^ 5 + 73 * (r:ℝ) ^ 5 := by
      rw [hK]; ring
    nlinarith
  · have q1 : ((r:ℝ) + 1) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by nlinarith
    have q2 : (r:ℝ) * n + 1 ≤ 2 * ((r:ℝ) * n) := by nlinarith
    have q : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) ≤
        4 * (r:ℝ) ^ 2 * (2 * ((r:ℝ) * n)) * (24 * r) :=
      mul_le_mul (mul_le_mul q1 q2 (by positivity) (by positivity)) h8 (by positivity) (by positivity)
    have e : 4 * (r:ℝ) ^ 2 * (2 * ((r:ℝ) * n)) * (24 * r) = 192 * ((r:ℝ) ^ 4 * n) := by ring
    have := mul_le_mul_of_nonneg_left q hc₃
    have : c₃ * ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) =
        c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1))) := by ring
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = (192 * c₃) * ((r:ℝ) ^ 4 * n) + (5 * C₂ + 7) * (r:ℝ) ^ 5 +
        ((24 * C₁ + 5 * C₂ + 80) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5) := by rw [hK]; ring
    have : 0 ≤ (24 * C₁ + 5 * C₂ + 80) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5 := by positivity
    nlinarith
  · have q : (2 * (r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) ≤ (3 * ((r:ℝ) * n)) * (24 * r) :=
      mul_le_mul (by nlinarith) h8 (by positivity) (by positivity)
    have e : (3 * ((r:ℝ) * n)) * (24 * r) = 72 * ((r:ℝ) ^ 2 * n) := by ring
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = 72 * ((r:ℝ) ^ 4 * n) + (5 * C₂ + 7) * (r:ℝ) ^ 5 +
        ((24 * C₁ + 192 * c₃ + 5 * C₂ + 8) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5) := by rw [hK]; ring
    have : 0 ≤ (24 * C₁ + 192 * c₃ + 5 * C₂ + 8) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5 := by positivity
    nlinarith

set_option maxHeartbeats 2000000 in
theorem top_density_threshold : C6.DensThreshTop := by
  intro C₁ C C₂ hC₁ hC
  set K : ℝ := 40 * C₁ + 80 + 12 * C + 4 * C * C₂ + 2 * (C₂ : ℝ) + 1 with hK
  refine ⟨⌈K⌉₊, ?_⟩
  intro CV hCV r n s al A hr hn hs hal hA
  have hKV : K ≤ (CV : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hCV)
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hsx : (s:ℝ) ≤ r + 1 := by exact_mod_cast hs
  have hal' : (al:ℝ) ≤ C₂ * (s:ℝ) ^ 2 := by exact_mod_cast hal
  have hy : (1:ℝ) ≤ n := by linarith
  have hK0 : 0 ≤ K := by positivity
  constructor
  · have hA' : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) ≤ A := by
      unfold C6.AV at hA
      have e : (r:ℝ) * ((CV:ℝ) * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
          (CV:ℝ) * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) + (CV:ℝ) * ((r:ℝ) ^ 4 * n) := by ring
      rw [e] at hA
      have : 0 ≤ (CV:ℝ) * ((r:ℝ) ^ 4 * n) := by positivity
      have : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) ≤ (CV:ℝ) * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_right hKV (by positivity)
      linarith
    have hs2 : (s:ℝ) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by
      have : (s:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
      nlinarith
    have hR2 : ((r:ℝ) + 1) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by nlinarith
    have x35 : (r:ℝ) ^ 3 ≤ (r:ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
    have hpos : (0:ℝ) < 5 * ((r:ℝ) + 1) := by positivity
    rw [le_sub_iff_add_le, le_div_iff₀ hpos, le_sub_iff_add_le]

    have b1 : (C₁ * (s:ℝ) ^ 2 + 2 * ((r:ℝ) + 1) ^ 2 + C * (r:ℝ) ^ 2) ≤ (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hs2 hC₁
      nlinarith
    have b2 : (C₁ * (s:ℝ) ^ 2 + 2 * ((r:ℝ) + 1) ^ 2 + C * (r:ℝ) ^ 2) * (5 * ((r:ℝ) + 1)) ≤
        (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 * (10 * r) :=
      mul_le_mul b1 (by linarith) (by positivity) (by positivity)
    have b3 : (r:ℝ) * al ≤ 4 * C₂ * (r:ℝ) ^ 3 := by
      have : (al:ℝ) ≤ C₂ * (4 * (r:ℝ) ^ 2) := le_trans hal' (mul_le_mul_of_nonneg_left hs2 (by positivity))
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ r)
      nlinarith
    have b4 : (n:ℝ) ^ 2 ≤ (r:ℝ) * n ^ 2 := by nlinarith [sq_nonneg (n:ℝ)]
    have b5 : C * ((n:ℝ) ^ 2 + (r:ℝ) ^ 3 + r * al) ≤ C * ((r:ℝ) * n ^ 2) + (C + 4 * C * C₂) * (r:ℝ) ^ 5 := by
      have : (n:ℝ) ^ 2 + (r:ℝ) ^ 3 + r * al ≤ (r:ℝ) * n ^ 2 + (1 + 4 * C₂) * (r:ℝ) ^ 5 := by nlinarith
      have := mul_le_mul_of_nonneg_left this hC
      nlinarith
    have e : (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 * (10 * r) = (40 * C₁ + 80 + 10 * C) * (r:ℝ) ^ 3 := by ring
    have b6 := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 40 * C₁ + 80 + 10 * C)
    have : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) = C * ((r:ℝ) * n ^ 2) + (C + 4 * C * C₂) * (r:ℝ) ^ 5 +
        (40 * C₁ + 80 + 10 * C) * (r:ℝ) ^ 5 +
        ((40 * C₁ + 80 + 11 * C + 4 * C * C₂ + 2 * C₂ + 1) * ((r:ℝ) * n ^ 2) + (C + 2 * C₂ + 1) * (r:ℝ) ^ 5) := by
      rw [hK]; ring
    have : 0 ≤ (40 * C₁ + 80 + 11 * C + 4 * C * C₂ + 2 * C₂ + 1) * ((r:ℝ) * n ^ 2) + (C + 2 * C₂ + 1) * (r:ℝ) ^ 5 := by
      positivity
    nlinarith
  · have hK2 : (2 * C₂ + 1 : ℝ) ≤ K := by
      rw [hK]; have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC) (Nat.cast_nonneg (α := ℝ) C₂); linarith
    have h2 : (2 * C₂ + 1 : ℝ) ≤ CV := le_trans hK2 hKV
    unfold C6.mmV
    have hR : ((C₂ * s ^ 2 + 1 : ℕ) : ℝ) ≤ ((CV * (r ^ 2 + 1) : ℕ) : ℝ) := by
      push_cast
      have q1 : (s:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
      have q2 : ((r:ℝ) + 1) ^ 2 ≤ 2 * ((r:ℝ) ^ 2 + 1) := by nlinarith [sq_nonneg ((r:ℝ) - 1)]
      have q3 : (C₂:ℝ) * (s:ℝ) ^ 2 ≤ (C₂:ℝ) * (2 * ((r:ℝ) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (le_trans q1 q2) (by positivity)
      have q4 : (2 * (C₂:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ (CV:ℝ) * ((r:ℝ) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have q5 : (1:ℝ) ≤ (r:ℝ) ^ 2 + 1 := by nlinarith
      nlinarith
    exact_mod_cast hR

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLeIntegralFsv
section
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

def isoQ : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun s := conj (Complex.I * s)
  invFun w := -Complex.I * conj w
  map_add' a b := by simp [mul_add]
  map_smul' c a := by
    simp only [RingHom.id_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  left_inv a := by
    simp only [map_mul, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp
  right_inv w := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  norm_map' s := by simp

theorem isoQ_apply (s : ℂ) : isoQ s = conj (Complex.I * s) := rfl

theorem fsv_smul (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by
  unfold P5.fsv
  simp [Circle.smul_def, isoQ_apply]
  left
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem norm_le_integral_fsv (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by
  have hc : (π⁻¹ : ℝ) ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hL : ∀ s : ℂ, (∫ u : ℂ, P5.fsv s u * φ u) = 𝓕 φ ((π⁻¹ : ℝ) • isoQ s) := by
    intro s
    rw [fourier_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => fsv_smul s u (φ u))
  have hmp : MeasurePreserving isoQ := isoQ.measurePreserving
  have hme : MeasurableEmbedding isoQ := isoQ.toHomeomorph.measurableEmbedding
  have hint1 : Integrable (fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) := by
    have h1 : Integrable ((fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) ∘ isoQ) := by
      have h2 := hΞ
      simp_rw [hL] at h2
      exact h2
    exact (hmp.integrable_comp_emb hme).mp h1
  have hint : Integrable (𝓕 φ) := by
    first
      | exact (integrable_comp_smul_iff volume (𝓕 φ) hc).mp hint1
      | exact (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℂ) (𝓕 φ) hc).mp hint1
      | exact (Integrable.comp_smul_iff hc).mp hint1
  have hinv : 𝓕⁻ (𝓕 φ) t = φ t := by
    first
      | exact hi.fourier_inversion hint hφ.continuousAt
      | exact hi.fourierInv_fourier_eq hint hφ.continuousAt
      | exact hφ.fourierInv_fourier_eq hi hint t
      | exact Continuous.fourierInv_fourier_eq hφ hi hint t
      | exact hi.fourierInv_fourier hint hφ.continuousAt
      | exact hφ.fourierInv_fourier hi hint t
      | exact MeasureTheory.Integrable.fourier_inversion hi hint hφ.continuousAt
  have hb : ‖φ t‖ ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := by
    rw [← hinv]
    first
      | rw [fourierInv_eq]
      | rw [Real.fourierInv_eq]
      | rw [fourierInv_eq']
      | rw [fourierInv_eq_fourier_neg, fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    first
      | exact Circle.norm_smul _ _
      | simp
  have e1 := hmp.integral_comp hme (fun s : ℂ => ‖𝓕 φ ((π⁻¹ : ℝ) • s)‖)
  have e2 := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => ‖𝓕 φ w‖) (π⁻¹ : ℝ)
  try dsimp only at e1
  try dsimp only at e2
  have heq : (∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖) =
      |((π⁻¹ : ℝ) ^ 2)⁻¹| • ∫ w : ℂ, ‖𝓕 φ w‖ := by
    simp_rw [hL]
    rw [e1, e2, Complex.finrank_real_complex]
  rw [heq, smul_eq_mul]
  have h0 : 0 ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ : 1 ≤ |((π⁻¹ : ℝ) ^ 2)⁻¹| := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  nlinarith

end Formalism.FourierDecayAlt.P.PBO
end
end


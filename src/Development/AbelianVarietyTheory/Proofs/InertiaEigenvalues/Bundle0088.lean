import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalisedPeriodAlgebraicEstimate
section
namespace GlobalTheory

theorem normalisedPeriod_algebraic_estimate :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t →
      (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z →
      (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) →
      ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  intro E _ _ n _ _ σ r M Mi Z a s t ha hs ht hσ hMMi hr hZ hM hD hrt i j
  set D := Mi - Z with hDdef
  set C := M * Z with hCdef
  have hC1 : C = 1 - M * D := by
    rw [hCdef, hDdef, Matrix.mul_sub, hMMi]; abel
  have hCσ : C.map σ = M.map σ * Z := by
    rw [hCdef, Matrix.map_mul, hZ]
  have hrC : r * C.map σ = C := by rw [hCσ, ← Matrix.mul_assoc, hr]
  have hX : C.map σ - 1 = -((M * D).map σ) := by
    rw [hC1, Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]; abel
  have hkey : σ (-C i j) - (-C i j) - (r - 1) i j = ((r - 1) * (C.map σ - 1)) i j := by
    have h2 : ((r - 1) * (C.map σ - 1)) = C - C.map σ - (r - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hrC, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul]; abel
    rw [h2]
    simp [Matrix.sub_apply, Matrix.map_apply, map_neg]
    ring
  have hMD : ∀ i j, ‖(M * D) i j‖ ≤ a * s :=
    GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n M D a s ha hs hM hD
  have hXb : ∀ i j, ‖(C.map σ - 1) i j‖ ≤ a * s := by
    intro i j
    rw [hX, Matrix.neg_apply, norm_neg, Matrix.map_apply, hσ]
    exact hMD i j
  rw [hkey]
  exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (r - 1) (C.map σ - 1) t (a * s) ht (mul_nonneg ha hs) hrt hXb i j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNorm
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Pw

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_pw_natCast (n : ℕ) (x : F) : pw p (n : ℤ) x = x ^ p ^ n := by
  simp [pw]

theorem coefDet_pw_pow_p (k : ℤ) (x : F) : pw p k x ^ p = pw p (k + 1) x := by
  unfold pw
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, if_pos (by omega), ← pow_mul, ← pow_succ]
    congr 2; omega
  · rw [if_neg hk]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-k).toNat = n + 1 := ⟨(-k).toNat - 1, by omega⟩
    rw [hn, Function.iterate_succ_apply']
    have e : ((frobeniusEquiv F p).symm (((frobeniusEquiv F p).symm)^[n] x)) ^ p =
        ((frobeniusEquiv F p).symm)^[n] x := by
      have := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[n] x)
      rwa [frobenius_def] at this
    rw [e]
    by_cases hk1 : 0 ≤ k + 1
    · rw [if_pos hk1]
      have hn0 : n = 0 := by omega
      have h0 : (k + 1).toNat = 0 := by omega
      rw [hn0, h0]; simp
    · rw [if_neg hk1]; congr 1; omega

theorem coefDet_pw_pow (k : ℤ) (x : F) (a : ℕ) : pw p k x ^ p ^ a = pw p (k + a) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, coefDet_pw_pow_p]
    congr 1; push_cast; ring

end Pw

section Det

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_det_scaled {h : ℕ} (a lam y : Fin h → F) :
    (Matrix.of fun r j : Fin h => (a r * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))).det =
      (∏ r, a r ^ p ^ (h - (r : ℕ))) * ((∏ j, y j ^ p ^ h) *
        (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det) := by
  rw [← Matrix.det_mul_row (fun j => y j ^ p ^ h), ← Matrix.det_mul_column (fun r => a r ^ p ^ (h - (r : ℕ)))]
  congr 1; ext r j
  simp only [Matrix.of_apply]
  have key : (y j ^ p ^ (r : ℕ)) ^ p ^ (h - (r : ℕ)) = y j ^ p ^ h := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le]
  rw [mul_pow, mul_pow, key]
  ring

theorem coefDet_det_rev {h : ℕ} (lam : Fin h → F) :
    (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin h)) : ℤ) : F) *
        (Matrix.of fun r j : Fin h => (lam j ^ p) ^ p ^ (r : ℕ)).det := by
  rw [← Matrix.det_permute]
  congr 1; ext r j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev, id]
  rw [← pow_mul, ← pow_succ']
  congr 2; have := r.isLt; omega

theorem coefDet_orth_pow {h : ℕ} (lam : Fin h → F) (hO : Orth p lam) : Orth p (fun j => lam j ^ p) := by
  intro c j hc
  have h1 := hO c j hc
  have e : (∑ i, (c i : F) * lam i) ^ p = ∑ i, (c i : F) * lam i ^ p := by
    rw [← frobenius_def (R := F) p, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, frobenius_def]
  show ‖lam j ^ p‖ ≤ ‖∑ i, (c i : F) * lam i ^ p‖
  rw [← e, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 p

theorem coefDet_norm_sign_cast {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

end Det

end GlobalTheory.PMonE

end

namespace GlobalTheory.PMonE
open Finset

theorem coefB_det (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (h : ℕ) (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hl : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hA : Antitone (fun j => ‖lam j‖)) (hO : Orth p lam) (L U : ℕ) :
    ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  set c : Fin h → F := fun r => lam r * π r ^ p ^ (r : ℕ) with hc
  have hc0 : ∀ r, c r ≠ 0 := fun r => mul_ne_zero (hl r) (pow_ne_zero _ (hπ r))
  have hA' : Antitone (fun j => ‖(fun j => lam j ^ p) j‖) := fun i j hij => by
    simp only [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hA hij) p
  have hDn : ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det‖ =
      ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
    rw [coefDet_det_rev, norm_mul, coefDet_norm_sign_cast, one_mul]
    have hM := mooreNorm F p h (fun j => lam j ^ p) hA' (coefDet_orth_pow p lam hO)
    rw [hM]
    refine prod_congr rfl fun j _ => ?_
    rw [norm_pow, ← pow_mul, ← pow_succ']; congr 2; have := j.isLt; omega
  have hD0 : (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det ≠ 0 := by
    rw [← norm_ne_zero_iff, hDn]
    exact (prod_pos fun j _ => pow_pos (norm_pos_iff.mpr (hl j)) _).ne'
  constructor
  · have e : coefB p ϖ lam π L U L = Matrix.of fun r j : Fin h =>
        ((c r)⁻¹ * (lam j * π j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, le_add_iff_nonneg_right, zero_le, if_true, sub_self, neg_zero,
        zpow_zero, mul_one, zero_mul, add_zero, coefDet_pw_natCast, hc]
      rw [div_eq_inv_mul]
    rw [e, coefDet_det_scaled, norm_mul, norm_mul, norm_prod, norm_prod, hDn]
    have hX : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) =
        (∏ j : Fin h, ‖π j‖ ^ p ^ h) * ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      rw [hc]
      simp only
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le, mul_comm]
    have hX0 : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) ≠ 0 :=
      (prod_pos fun r _ => pow_pos (norm_pos_iff.mpr (hc0 r)) _).ne'
    simp only [norm_pow, norm_inv, inv_pow]
    rw [prod_inv_distrib, ← hX, inv_mul_cancel₀ hX0]
  · set y : Fin h → F := fun j => pw p (-((L : ℤ) * h)) (π j) with hy
    have hy0 : ∀ j, y j ≠ 0 := by
      intro j hyj
      have h1 := coefDet_pw_pow p (-((L : ℤ) * h)) (π j) (L * h)
      have h0 : pw p (0 : ℤ) (π j) = π j := by simp [pw]
      rw [show pw p (-((L : ℤ) * h)) (π j) = y j from rfl, hyj,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
      push_cast at h1
      rw [neg_add_cancel, h0] at h1
      exact hπ j h1.symm
    have e : coefB p ϖ lam π L U 0 = Matrix.of fun r j : Fin h =>
        ((ϖ ^ L / c r) * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, zero_le, if_true, hc, hy, coefDet_pw_pow]
      have e1 : ((r : ℕ) : ℤ) + (((0 : ℕ) : ℤ) - L) * h = -((L : ℤ) * h) + ((r : ℕ) : ℤ) := by
        push_cast; ring
      have e2 : ϖ ^ (-(((0 : ℕ) : ℤ) - L)) = ϖ ^ L := by
        rw [show -(((0 : ℕ) : ℤ) - L) = (L : ℤ) by push_cast; ring, zpow_natCast]
      rw [e1, e2]
      congr 1
      ring
    rw [e, coefDet_det_scaled]
    exact mul_ne_zero (prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hϖ) (hc0 r)))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)) hD0)

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicator
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourGUnit

variable {F : Type} [NontriviallyNormedField F]

theorem integral_ball_char {r : ℕ} [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] [ProperSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) (v : Fin r → F) :
    ∫ x, {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => μ) =
      {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator 1 v := by
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  have hS : S = Set.univ.pi fun _ => Metric.closedBall (0 : F) 1 := by
    ext x; simp [S, Metric.mem_closedBall]
  have hSm : MeasurableSet S := hS ▸ MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, integral_indicator hSm,
      setIntegral_congr_fun hSm (g := fun _ => (1 : ℂ)) (fun x hx => ?_), setIntegral_const]
    · rw [Measure.real, hS, Measure.pi_pi]
      simp [hvol]
    · apply hψ.1
      rw [dotProduct]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro i _
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hv i)
  · rw [Set.indicator_of_notMem hv]
    obtain ⟨i, hi⟩ : ∃ i, 1 < ‖v i‖ := by
      simp only [S, Set.mem_setOf_eq, not_forall, not_le] at hv; exact hv
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    have hvi : v i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; linarith
    set z₀ : Fin r → F := Pi.single i (x₀ * (v i)⁻¹) with hz₀def
    have hz₀ : z₀ ∈ S := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hz₀def, Pi.single_eq_same]
        apply hx₀'
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hi
      · rw [hz₀def, Pi.single_eq_of_ne hj, norm_zero]; exact zero_le_one
    have hχ : ψ (z₀ ⬝ᵥ v) ≠ 1 := by
      rw [hz₀def, single_dotProduct, mul_assoc, inv_mul_cancel₀ hvi, mul_one]
      exact hx₀
    have hadd : ∀ a b : Fin r → F, a ∈ S → b ∈ S → a + b ∈ S := fun a b ha hb i =>
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    have key : ∀ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) (z + z₀) =
        S.indicator (fun x => ψ (x ⬝ᵥ v)) z * ψ (z₀ ⬝ᵥ v) := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem (hadd _ _ hz hz₀), Set.indicator_of_mem hz, add_dotProduct,
          AddChar.map_add_eq_mul]
      · have hneg : -z₀ ∈ S := fun j => by rw [Pi.neg_apply, norm_neg]; exact hz₀ j
        have : z + z₀ ∉ S := fun h => hz (by simpa using hadd _ _ h hneg)
        rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hz, zero_mul]
    have h := integral_add_right_eq_self (μ := Measure.pi fun _ : Fin r => μ)
      (fun z => S.indicator (fun x => ψ (x ⬝ᵥ v)) z) z₀
    simp only [key, integral_mul_const] at h
    have h2 : (∫ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) z ∂(Measure.pi fun _ => μ)) * (ψ (z₀ ⬝ᵥ v) - 1) = 0 := by
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hχ

end GlobalTheory.JR.FourGUnit

namespace GlobalTheory.JR

open FourGUnit in

theorem fourG_unitG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by
  intro F E _ _ _ _ U r M ψ hψ
  letI := M.mF
  haveI := M.bF
  haveI := U.ultraF
  haveI := U.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI := M.haarF
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  unfold fourG
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧
    ‖Y.2.2.2‖ ≤ 1} with hTdef
  have hT : unitG r F = T.indicator 1 := rfl
  by_cases hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1
  · have hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') =
        S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c' := by
      intro b' c'
      by_cases hb' : b' ∈ S
      · by_cases hc' : c' ∈ S
        · rw [hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩),
            Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul,
            AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]
        · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1),
            Set.indicator_of_notMem hc', zero_mul, mul_zero]
      · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1),
          Set.indicator_of_notMem hb', zero_mul, zero_mul]
    have hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) =
        S.indicator 1 v := integral_ball_char M.μF M.volF ψ hψ
    simp_rw [hint, integral_const_mul, hball, integral_mul_const, hball]
    by_cases hb : b ∈ S
    · by_cases hc : c ∈ S
      · rw [hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩),
          Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1),
          Set.indicator_of_notMem hc, zero_mul]
    · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1),
        Set.indicator_of_notMem hb, mul_zero]
  · have h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0 := by
      intro b' c'
      rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩),
        zero_mul]
    simp_rw [h0, integral_zero]
    rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]

end GlobalTheory.JR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockHasCompactSupport
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourU_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  intro F E _ _ _ _ hUn r M ψ hψ htr f hf hloc
  obtain ⟨U, hU, hfU⟩ := hloc
  haveI : CharZero F := hUn.charZero
  haveI : LocallyCompactSpace E := hUn.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set a : E := algebraMap F E (x₀ / 2) with ha
  have htra : Algebra.trace F E a = x₀ := by
    apply (algebraMap F E).injective
    rw [htr a, ha, hUn.star_fix, ← map_add, add_halves]

  have hcont : Continuous (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) := by
    fun_prop
  have hpre : (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → E) :=
    hcont.tendsto 0 hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre

  have hzero : ∀ X : Hn r F E, ∀ i, ‖a‖ / δ < ‖X.2.1 i‖ → fourU M ψ f X = 0 := by
    intro X i hi
    have hbi : X.2.1 i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; exact absurd hi (not_lt.2 (by positivity))
    set t : Fin r → E := Pi.single i (star (a / X.2.1 i)) with ht
    have htn : ‖t‖ < δ := by
      rw [ht, Pi.norm_single, hUn.norm_star, norm_div]
      rw [div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hδ] at hi
      linarith
    have htU : ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F)) ∈ U :=
      hball (mem_ball_zero_iff.2 htn)
    have hst : star t ⬝ᵥ X.2.1 = a := by
      rw [ht, ← Pi.single_star, single_dotProduct, star_star, div_mul_cancel₀ _ hbi]
    have hshift : ∀ c, f (X.1, t + c, X.2.2) = f (X.1, c, X.2.2) := by
      intro c
      have := hfU (X.1, c, X.2.2) _ htU
      rw [← this]
      congr 1
      ext <;> simp [add_comm]
    have hchar : ∀ c : Fin r → E, ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) =
        ψ x₀ * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) := by
      intro c
      rw [star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul, hst, htra]
    have key : fourU M ψ f X = ψ x₀ * fourU M ψ f X := by
      simp only [fourU]
      calc ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
          = ∫ c, f (X.1, t + c, X.2.2) * ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE) :=
            (integral_add_left_eq_self (fun c => f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) t).symm
        _ = ∫ c, ψ x₀ * (f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) ∂(Measure.pi fun _ : Fin r => M.μE) := by
            congr 1; funext c; rw [hshift, hchar]; ring
        _ = _ := integral_const_mul _ _
    have h1 : (1 - ψ x₀) * fourU M ψ f X = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hx₀
    · exact h

  have hzero2 : ∀ X : Hn r F E, (∀ c, f (X.1, c, X.2.2) = 0) → fourU M ψ f X = 0 := by
    intro X h
    simp [fourU, h]
  have hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ (Metric.closedBall (0 : Fin r → E) (‖a‖ / δ) ×ˢ
      ((fun Y : Hn r F E => Y.2.2) '' tsupport f))) :=
    (hf.2.image continuous_fst).prod ((isCompact_closedBall _ _).prod (hf.2.image (by fun_prop)))
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra hne
  apply hX
  refine ⟨?_, ?_, ?_⟩
  · by_contra h1
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h1 ⟨_, hc, rfl⟩)
  · rw [mem_closedBall_zero_iff]
    by_contra h2
    have hR : 0 ≤ ‖a‖ / δ := by positivity
    rw [pi_norm_le_iff_of_nonneg hR] at h2
    push_neg at h2
    obtain ⟨i, hi⟩ := h2
    exact hne (hzero X i hi)
  · by_contra h3
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h3 ⟨_, hc, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockIsLocallyConstant
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourU_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f →
    (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ htr f hf ⟨U, hU0, hUf⟩
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)

  have htr1 : ∀ d : E, ‖d‖ ≤ 1 → ψ (Algebra.trace F E d) = 1 := by
    intro d hd
    apply hψ.1
    have h1 : ‖algebraMap F E (Algebra.trace F E d)‖ ≤ 1 := by
      rw [htr]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd ?_)
      rw [Unram.norm_star (F := F)]; exact hd
    rwa [norm_algebraMap'] at h1

  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin r → E)).1
    ((hf.2.isCompact.image (continuous_fst.comp continuous_snd)).isBounded)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X₀
  have hcont : Continuous fun X : Hn r F E => ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) :=
    (continuous_fst.sub continuous_const).prodMk (continuous_const.prodMk
      ((continuous_snd.comp continuous_snd).sub continuous_const))
  have hV1 : ∀ᶠ X in 𝓝 X₀, ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) ∈ U := by
    have : ((X₀.1 - X₀.1, (0 : Fin r → E), X₀.2.2 - X₀.2.2) : Hn r F E) = 0 := by
      ext <;> simp
    exact hcont.continuousAt.preimage_mem_nhds (by rw [this]; exact hU0)
  have hV2 : ∀ᶠ X in 𝓝 X₀, X.2.1 ∈ Metric.closedBall X₀.2.1 (1 / R') :=
    (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))
  filter_upwards [hV1, hV2] with X hX1 hX2
  unfold fourU
  congr 1
  funext c
  have hfe : f (X.1, c, X.2.2) = f (X₀.1, c, X₀.2.2) := by
    have := hUf (X₀.1, c, X₀.2.2) _ hX1
    rw [← this]; congr 1; ext <;> simp
  rw [hfe]
  by_cases h0 : f (X₀.1, c, X₀.2.2) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 1
  have hc : ‖c‖ ≤ R := by
    have hmem : c ∈ (fun X : Hn r F E => X.2.1) '' tsupport f :=
      ⟨(X₀.1, c, X₀.2.2), subset_tsupport _ h0, rfl⟩
    simpa using hR hmem
  have hs : ‖star c ⬝ᵥ (X.2.1 - X₀.2.1)‖ ≤ 1 := by
    have hd : ‖X.2.1 - X₀.2.1‖ ≤ 1 / R' := by rw [← dist_eq_norm]; exact hX2
    unfold dotProduct
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
    have h1 : ‖c i‖ ≤ R' := (norm_le_pi_norm c i).trans (hc.trans (le_max_left _ _))
    have h2 : ‖(X.2.1 - X₀.2.1) i‖ ≤ 1 / R' := (norm_le_pi_norm _ i).trans hd
    calc ‖c i‖ * ‖(X.2.1 - X₀.2.1) i‖ ≤ R' * (1 / R') :=
          mul_le_mul h1 h2 (norm_nonneg _) hR'pos.le
      _ = 1 := by field_simp
  have hsplit : star c ⬝ᵥ X.2.1 = star c ⬝ᵥ X₀.2.1 + star c ⬝ᵥ (X.2.1 - X₀.2.1) := by
    rw [dotProduct_sub]; ring
  rw [hsplit, map_add, AddChar.map_add_eq_mul, htr1 _ hs, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPowOfPowPowEqSelfStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_apply_eq_pow_prime_pow : ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N → ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  first | exact @GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self | exact GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self | (intros; apply GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltrationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  first | exact @GlobalTheory.semilinear_iterate_prime_pow_sub_mem | exact GlobalTheory.semilinear_iterate_prime_pow_sub_mem | (intros; apply GlobalTheory.semilinear_iterate_prime_pow_sub_mem <;> assumption)
end


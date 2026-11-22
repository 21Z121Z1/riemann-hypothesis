import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
section
open Formalism.BasicNotions.TH
open scoped Kronecker

namespace GlobalTheory.FockPair

theorem fockAct1_eq_kron (p q r s : ℕ) (Y : Mat p q) :
    fockAct1 p q r s Y = omAct p q r s (Y ⊗ₖ (1 : Mat r s)) := rfl

theorem fockAct2_eq_kron (p q r s : ℕ) (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s ((1 : Mat p q) ⊗ₖ Z) := rfl

theorem pair_lie_commute : ∀ (p q r s : ℕ), IsLieAct (fockAct1 p q r s) ∧
    IsLieAct (fockAct2 p q r s) ∧ ∀ (Y : Mat p q) (Z : Mat r s),
      fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  intro p q r s
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩
  · rw [map_sub]
    simp only [fockAct1_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [map_sub]
    simp only [fockAct2_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← GlobalTheory.T.fockQuadraticAction_map_lie_bracket,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end GlobalTheory.FockPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLe
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockAnalytic

theorem totalDegree_pderiv_le_self {σ : Type} (i : σ) (Q : MvPolynomial σ ℂ) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  refine Finset.sup_le fun m hm => ?_
  have hc : coeff (m + Finsupp.single i 1) Q ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := le_totalDegree (mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ Q.totalDegree
  omega

def OneStep {σ : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (A : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d →
    (A P).totalDegree ≤ d + 1 ∧ ‖ι (A P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2

section
variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem oneStep_mul (h : IsFockIP ι) (i : σ) : OneStep ι (LinearMap.mulLeft ℂ (X i)) := by
  intro d P hP
  refine ⟨?_, (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).1⟩
  rw [LinearMap.mulLeft_apply]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]; omega

theorem oneStep_pderiv (h : IsFockIP ι) (i : σ) : OneStep ι (pderiv i).toLinearMap := by
  intro d P hP
  refine ⟨((totalDegree_pderiv_le_self i P).trans hP).trans (Nat.le_succ _), ?_⟩
  have := (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).2
  have h2 := sq_nonneg ‖ι P‖
  change ‖ι (pderiv i P)‖ ^ 2 ≤ _
  nlinarith

omit [DecidableEq σ] in
theorem OneStep.neg {A : Module.End ℂ (MvPolynomial σ ℂ)} (h : OneStep ι A) : OneStep ι (-A) := by
  intro d P hP
  simpa using h d P hP

omit [DecidableEq σ] in
theorem OneStep.comp {A B : Module.End ℂ (MvPolynomial σ ℂ)} (hA : OneStep ι A) (hB : OneStep ι B)
    (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ((A * B) P).totalDegree ≤ d + 2 ∧ ‖ι ((A * B) P)‖ ≤ ((d : ℝ) + 3 / 2) * ‖ι P‖ := by
  obtain ⟨h1, h2⟩ := hB d P hP
  obtain ⟨h3, h4⟩ := hA (d + 1) _ h1
  refine ⟨h3, ?_⟩
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  push_cast at h4
  have h5 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (d : ℝ) + 1 + 1 by positivity)
  have h6 := sq_nonneg ‖ι P‖
  change ‖ι (A (B P))‖ ^ 2 ≤ _
  nlinarith
end

section
variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Pol p q r s →ₗ[ℂ] H}

theorem omE_bound (h : IsFockIP ι) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s)
    (hP : P.totalDegree ≤ d) :
    (omE l l' P).totalDegree ≤ d + 2 ∧ ‖ι (omE l l' P)‖ ≤ ((d : ℝ) + 2) * ‖ι P‖ := by
  have hA : OneStep ι (raiB l) := by
    unfold raiB; split_ifs
    exacts [oneStep_mul h l, (oneStep_pderiv h l).neg]
  have hB : OneStep ι (lowB l') := by
    unfold lowB; split_ifs
    exacts [oneStep_pderiv h l', oneStep_mul h l']
  obtain ⟨h1, h2⟩ := hA.comp hB d P hP
  have hn := norm_nonneg (ι P)
  unfold omE
  split_ifs
  · rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    refine ⟨(totalDegree_add _ _).trans (max_le h1 ((totalDegree_smul_le _ _).trans (by omega))), ?_⟩
    rw [map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  · rw [add_zero]
    exact ⟨h1, by linarith⟩

theorem omAct_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ)
    (P : Pol p q r s) (hP : P.totalDegree ≤ d) :
    (omAct p q r s Y P).totalDegree ≤ d + 2 ∧
      ‖ι (omAct p q r s Y P)‖ ≤ (∑ l, ∑ l', ‖Y l l'‖) * (((d : ℝ) + 2) * ‖ι P‖) := by
  have e : omAct p q r s Y P = ∑ l, ∑ l', Y l l' • omE l l' P := by
    simp [omAct, LinearMap.sum_apply]
  rw [e]
  constructor
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l' _ => ?_)
    exact (totalDegree_smul_le _ _).trans (omE_bound h l l' d P hP).1
  · rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l' _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (omE_bound h l l' d P hP).2 (norm_nonneg _)

theorem omAct_pow_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d m : ℕ)
    (hm : d ≤ 2 * m) (P : Pol p q r s) (hP : P.totalDegree ≤ d) (k : ℕ) :
    ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧
      ‖ι ((omAct p q r s Y ^ k) P)‖ ≤
        (2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖ := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := omAct_bound h Y _ _ ih.1
    refine ⟨by omega, h2.trans ?_⟩
    have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
    have hm' : (d : ℝ) ≤ 2 * m := by exact_mod_cast hm
    rw [Nat.ascFactorial_succ]
    push_cast
    calc _ ≤ (∑ l, ∑ l', ‖Y l l'‖) * ((2 * ((m : ℝ) + 1 + k)) *
            ((2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS
          exact mul_le_mul (by linarith) ih.2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
end

theorem omAct_pow_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  intro p q r s H _ _ ι h Y d k P hP
  obtain ⟨h1, h2⟩ := omAct_pow_bound h Y d ((d + 1) / 2) (by omega) P hP k
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  set m := (d + 1) / 2 with hm
  have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
  generalize (∑ l, ∑ l', ‖Y l l'‖) = S at hS
  have hm1 : (m : ℝ) ≤ (d : ℝ) / 2 + 1 := by
    have : 2 * m ≤ d + 2 := by omega
    have : (2 * m : ℝ) ≤ d + 2 := by exact_mod_cast this
    linarith
  have h3 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ ((d : ℝ) / 2 + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hm1
  have h4 : (((m + k).choose k : ℕ) : ℝ) ≤ 2 ^ (m + k) := by
    exact_mod_cast Nat.choose_le_two_pow (m + k) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  calc (2 * S) ^ k * ((k.factorial : ℝ) * ((m + k).choose k : ℝ))
      ≤ (2 * S) ^ k * ((k.factorial : ℝ) * 2 ^ (m + k)) := by gcongr
    _ = (4 * S) ^ k * (k.factorial : ℝ) * 2 ^ m := by
        rw [show (4 : ℝ) * S = 2 * (2 * S) by ring, mul_pow 2 (2 * S), pow_add]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.FockAnalytic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjoint
section
noncomputable section

open MvPolynomial Matrix Formalism.L2.DIV

namespace GlobalTheory.MinorFrame

variable {σ σ' : Type} [Fintype σ] [Fintype σ']

theorem constantCoeff_rsub (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ' ℂ →+* ℂ).comp (rsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [rsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_rsub [DecidableEq σ] [DecidableEq σ'] (M : Matrix σ' σ ℂ) (s : σ') (g : MvPolynomial σ ℂ) :
    pderiv s (rsub M g) = ∑ w, C (M s w) * rsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (rsub M (X k)) = C (M s k) := by
      rw [rsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_rsub_adj (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ) :
    fockL (rsub M F) F' = fockL F (rsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_rsub]
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : rsub M (p * X v) = ∑ w, M w v • (X w * rsub M p) := by
      rw [map_mul, rsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    rw [mul_comm p, fockL_X_pderiv, pderiv_rsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem fockS_rsub_adj : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ)
    (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' =
      Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  intro σ σ' _ _ M F F'
  exact fockL_rsub_adj M F F'

end GlobalTheory.MinorFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExp
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

theorem hasDerivAt_exp_ofReal_smul_entry {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (i j : Fin a) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp ((h : ℂ) • S) i j) (S i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) S 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  simp only [Complex.coe_smul]
  exact h2

theorem colDer_mul_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (v : Var ι d a) :
    colDer τ S (R * X v) = colDer τ S R * X v + R * colDer τ S (X v) := by
  simp only [colDer_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_mul]
  simp only [smul_eq_C_mul]
  ring

theorem hasDerivAt_coeff_mul_X {σ : Type} {A : ℝ → MvPolynomial σ ℂ} {B : MvPolynomial σ ℂ}
    (hA : ∀ m, HasDerivAt (fun h => coeff m (A h)) (coeff m B) 0) (w : σ) (m : σ →₀ ℕ) :
    HasDerivAt (fun h => coeff m (A h * X w)) (coeff m (B * X w)) 0 := by
  classical
  simp only [coeff_mul_X']
  split_ifs
  · exact hA _
  · exact hasDerivAt_const _ _

theorem hasDerivAt_coeff_colSub_of_curve [Fintype ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ)
    (g : ℝ → ι → Matrix (Fin a) (Fin a) ℂ) (h0 : g 0 = 1)
    (hg : ∀ σ i j, HasDerivAt (fun h => g h σ i j) (if σ = τ then S i j else 0) 0)
    (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (g h) R)) (coeff m (colDer τ S R)) 0 := by
  have hone : ∀ P : Pol ι d a, colSub (g 0) P = P := by
    have : (colSub (g 0) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro y
      rw [h0]
      simp only [colSub, aeval_X, Pi.one_apply, AlgHom.id_apply]
      rw [Finset.sum_eq_single y.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    intro P
    rw [this, AlgHom.id_apply]
  induction R using MvPolynomial.induction_on generalizing m with
  | C c =>
    have h1 : colDer τ S (C c : Pol ι d a) = 0 := by simp [colDer_apply]
    simp only [h1, algHom_C, coeff_zero]
    exact hasDerivAt_const _ _
  | add P Q hP hQ =>
    simp only [map_add, coeff_add]
    exact (hP m).add (hQ m)
  | mul_X P v hP =>
    have e1 : ∀ h, coeff m (colSub (g h) (P * X v)) =
        ∑ k, g h v.1 k v.2.2 * coeff m (colSub (g h) P * X (v.1, v.2.1, k)) := by
      intro h
      rw [map_mul]
      conv_lhs => rw [show colSub (g h) (X v : Pol ι d a) = ∑ k, C (g h v.1 k v.2.2) * X (v.1, v.2.1, k) by
        simp [colSub]]
      rw [Finset.mul_sum, coeff_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, coeff_C_mul]
    simp only [e1]
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hg v.1 k v.2.2).fun_mul (hasDerivAt_coeff_mul_X hP (v.1, v.2.1, k) m)
    refine hd.congr_deriv ?_
    rw [colDer_mul_X, coeff_add, Finset.sum_add_distrib, add_comm]
    congr 1
    · rw [h0, Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    · rw [colDer_X, hone]
      by_cases hv : v.1 = τ
      · subst hv
        simp only [if_true, Finset.mul_sum, coeff_sum, mul_smul_comm, coeff_smul, smul_eq_mul]
      · simp [hv]

theorem hasDerivAt_coeff_colSub_exp {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι)
    (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (coeff m (colDer τ S R)) 0 := by
  refine hasDerivAt_coeff_colSub_of_curve τ S (fun h => atPl τ (NormedSpace.exp ((h : ℂ) • S))) ?_ ?_ R m
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, atPl]
    exact Function.update_eq_self τ 1
  · intro σ i j
    by_cases h : σ = τ
    · subst h
      simp only [atPl, Function.update_self, if_true]
      exact hasDerivAt_exp_ofReal_smul_entry S i j
    · simp only [atPl, Function.update_of_ne h, if_neg h]
      exact hasDerivAt_const _ _

end GlobalTheory.ColLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinMovedPoint
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t z hk ha hz
  have hw : (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) ∈ upperHalf F := fun i ↦ (hz i).2
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_shiftedLattice_fourier F k 𝔞 𝔟 a₀ a x _ hk ha hw
  have h2 := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 x) (LinearEquiv.refl F _)
    (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) (fun i ↦ τ + t * z i / (1 + z i * c)) 1
    (fun i ↦ 1 + z i * c) hk (fun _ ↦ Iff.rfl) (fun i ↦ (hz i).1) (fun v i ↦ by
      have := (hz i).1
      simp only [coord, LinearEquiv.refl_apply, Pi.one_apply]
      field_simp
      ring)
  have h3 := h1.mul_left ((∏ i, (1 + z i * c))⁻¹ ^ k)
  rw [h2]
  convert h3 using 1
  · rfl
  · funext ξ
    have hq : qPow ξ (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) =
        Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
          ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) := by
      rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F ξ]
      unfold qPow
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hq, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
    ring
  · ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam

theorem derivWeierstrassP_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  rw [← L.deriv_weierstrassP, ← L'.deriv_weierstrassP, Formalism.L2.Th1.F.LatOnly.wp_eq h]

theorem derivWeierstrassP_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  have hs := Formalism.L2.Th1.F.Homog.tsum_scale L c hc (fun w => 2 / (c * z - w) ^ 3)
  rw [hs]
  have hterm : ∀ l : L.lattice, 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3) := by
    intro l
    rw [← mul_sub, mul_pow, div_mul_eq_div_div, div_eq_inv_mul (2 / c ^ 3), div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  ring

theorem lattice_eq_scalePair_tauPair {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.lattice = (scalePair (tauPair τ) c h.1).lattice := by
  ext x
  rw [h.2 x, Formalism.L2.Th1.F.Homog.mem_scale, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨u, v, rfl⟩
    refine ⟨u, v, ?_⟩
    change (u : ℂ) * (τ : ℂ) + (v : ℂ) * 1 = c⁻¹ * (c * ((u : ℂ) * (τ : ℂ) + (v : ℂ)))
    rw [← mul_assoc, inv_mul_cancel₀ h.1, one_mul, mul_one]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (τ : ℂ) + (n : ℂ) * 1 = c⁻¹ * x at hmn
    rw [mul_one] at hmn
    rw [hmn, ← mul_assoc, mul_inv_cancel₀ h.1, one_mul]

theorem homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  intro L c τ h
  have hl := lattice_eq_scalePair_tauPair h
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hl, Formalism.L2.Th1.F.Homog.mem_scale, ← mul_assoc, inv_mul_cancel₀ h.1, one_mul]
  · rw [Formalism.L2.Th1.F.LatOnly.wp_eq hl, Formalism.L2.Th1.F.Homog.wp_scale]
  · rw [derivWeierstrassP_eq_of_lattice_eq hl, derivWeierstrassP_scalePair]
  · rw [Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq hl, Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale]
  · rw [Formalism.L2.Th1.F.LatOnly.area_eq hl, Formalism.L2.Th1.F.Homog.area_scale]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerFontaineThetaEqSpanOfDistinguishedStatement
section
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_fontaineTheta_eq_span_of_distinguished : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) → ∀ ξ : WittVector p (PreTilt R p), fontaineTheta R p ξ = 0 → (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff ξ ∣ c) → RingHom.ker (fontaineTheta R p) = Ideal.span {ξ} := by
  first | exact @GlobalTheory.ker_fontaineTheta_eq_span_of_dvd | exact GlobalTheory.ker_fontaineTheta_eq_span_of_dvd | (intros; apply GlobalTheory.ker_fontaineTheta_eq_span_of_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIffStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime], q.comap (algebraMap R A) = maximalIdeal R → ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔ (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  first | exact @GlobalTheory.StrictHensel.strictlyHenselian_iff | exact GlobalTheory.StrictHensel.strictlyHenselian_iff | (intros; apply GlobalTheory.StrictHensel.strictlyHenselian_iff <;> assumption)
end


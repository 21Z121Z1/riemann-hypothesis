import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermsSameDoubleCosetSameDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandValuesShift
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.GelfValSym

theorem tot_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, M a b = (fun _ => (1 : ℂ)) ⬝ᵥ (M *ᵥ fun _ => (1 : ℂ)) := by
  simp [dotProduct, mulVec]

theorem amat_add_const {n : ℕ} (l : Fin n → ℂ) (t : ℂ) :
    Formalism.REAL.Amat (fun a => l a + t) = Formalism.REAL.Amat l + t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Formalism.REAL.Amat]
  · simp [Formalism.REAL.Amat, h, Matrix.one_apply_ne h]

theorem rowdiff {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (b : Fin n) :
    Formalism.REAL.Amat l p b - Formalism.REAL.Amat l q b =
      if b = p then l p else if b = q then -1 - l q else 0 := by
  simp only [Formalism.REAL.Amat, Matrix.of_apply]
  by_cases hbp : b = p
  · subst hbp
    have h1 : q ≠ b := by intro h; rw [h] at hpq; omega
    have h2 : ¬ q < b := by rw [Fin.lt_def]; omega
    simp [h1, h2]
  · by_cases hbq : b = q
    · subst hbq
      have h2 : p < b := by rw [Fin.lt_def]; omega
      have h3 : p ≠ b := Ne.symm hbp
      simp [hbp, h2, h3]
    · have e1 : p ≠ b := Ne.symm hbp
      have e2 : q ≠ b := Ne.symm hbq
      simp only [e1, e2, hbp, hbq, if_false]
      have : (p < b ↔ q < b) := by
        rw [Fin.lt_def, Fin.lt_def]
        have : b.val ≠ p.val := fun h => hbp (Fin.ext h)
        have : b.val ≠ q.val := fun h => hbq (Fin.ext h)
        omega
      by_cases h : q < b
      · simp [h, this.mpr h]
      · simp [h, mt this.mp h]

theorem coldiff {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (a : Fin n) :
    Formalism.REAL.Amat (l ∘ Equiv.swap p q) a p - Formalism.REAL.Amat (l ∘ Equiv.swap p q) a q =
      if a = p then l q + 1 else if a = q then - l p else 0 := by
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  simp only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]
  by_cases hap : a = p
  · subst hap
    have h2 : a < q := by rw [Fin.lt_def]; omega
    simp [hne, h2]
  · by_cases haq : a = q
    · subst haq
      have h1 : ¬ a < p := by rw [Fin.lt_def]; omega
      simp [hap, h1, Equiv.swap_apply_right]
    · simp only [hap, haq, if_false]
      have : (a < p ↔ a < q) := by
        rw [Fin.lt_def, Fin.lt_def]
        have : a.val ≠ p.val := fun h => hap (Fin.ext h)
        have : a.val ≠ q.val := fun h => haq (Fin.ext h)
        omega
      by_cases h : a < p
      · simp [h, this.mp h]
      · simp [h, mt this.mpr h]

theorem amat_sub_swap {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (a b : Fin n) :
    Formalism.REAL.Amat l a b - Formalism.REAL.Amat (l ∘ Equiv.swap p q) a b =
      if a = b then l a - l (Equiv.swap p q a) else 0 := by
  simp only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> ring

theorem w_vecMul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (b : Fin n) :
    ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) ᵥ* M) b = M p b - M q b := by
  simp [vecMul, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib]

theorem w_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (a : Fin n) :
    (M *ᵥ (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ)) a = M a p - M a q := by
  simp [mulVec, dotProduct, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem amat_swap_semiconj {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1)
    (t : ℂ) (ht : t * (l p - l q - 1) = l p - l q) :
    (1 - t • vecMulVec (Pi.single p 1 - Pi.single q 1) (Pi.single p 1 - Pi.single q 1)) * Formalism.REAL.Amat l =
      Formalism.REAL.Amat (l ∘ Equiv.swap p q) *
        (1 - t • vecMulVec (Pi.single p 1 - Pi.single q 1) (Pi.single p 1 - Pi.single q 1)) := by
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  rw [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec]
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [w_vecMul, w_mulVec, rowdiff l p q hpq, coldiff l p q hpq]
  have hd := amat_sub_swap l p q a b
  rw [← sub_eq_zero]
  have key : (if a = b then l a - l (Equiv.swap p q a) else 0) -
      t * ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a *
        (if b = p then l p else if b = q then -1 - l q else 0)) +
      t * ((if a = p then l q + 1 else if a = q then - l p else 0) *
        (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) b) = 0 := by
    simp only [Pi.sub_apply, Pi.single_apply]
    have hqp : q ≠ p := Ne.symm hne
    by_cases hab : a = b
    · subst hab
      by_cases hap : a = p
      · subst hap; simp [hne]; linear_combination -ht
      · by_cases haq : a = q
        · subst haq; simp [hqp, Equiv.swap_apply_right]; linear_combination ht
        · simp [hap, haq, Equiv.swap_apply_of_ne_of_ne hap haq]
    · by_cases hap : a = p <;> by_cases haq : a = q <;> by_cases hbp : b = p <;> by_cases hbq : b = q <;>
        (try subst hap) <;> (try subst haq) <;> (try subst hbp) <;> (try subst hbq) <;>
        simp_all <;> first | ring | linear_combination ht | linear_combination -ht | linear_combination (2 : ℂ) * ht | linear_combination (-2 : ℂ) * ht
  linear_combination key + hd

theorem tot_swap_of {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1)
    (hd : l p - l q - 1 ≠ 0) (k : ℕ) :
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  set t : ℂ := (l p - l q) / (l p - l q - 1) with ht_def
  have ht : t * (l p - l q - 1) = l p - l q := by rw [ht_def]; field_simp
  set w : Fin n → ℂ := Pi.single p 1 - Pi.single q 1 with hw
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  have hsum : ∑ c, w c = 0 := by simp [hw, Finset.sum_sub_distrib]
  set Q : Matrix (Fin n) (Fin n) ℂ := 1 - t • vecMulVec w w with hQ_def
  have hQ : SemiconjBy Q (Formalism.REAL.Amat l) (Formalism.REAL.Amat (l ∘ Equiv.swap p q)) :=
    amat_swap_semiconj l p q hpq t ht
  have hk := hQ.pow_right k
  have hl : (fun _ => (1 : ℂ)) ᵥ* Q = fun _ => 1 := by
    funext b
    simp only [hQ_def, vecMul_sub, vecMul_one, vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : ((fun _ => (1 : ℂ)) ᵥ* vecMulVec w w) b = 0 := by
      simp [vecMul, dotProduct, vecMulVec_apply, ← Finset.sum_mul, hsum]
    rw [this, mul_zero, sub_zero]
  have hr : Q *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1 := by
    funext a
    simp only [hQ_def, sub_mulVec, one_mulVec, Pi.sub_apply]
    have : ((t • vecMulVec w w) *ᵥ (fun _ => (1 : ℂ))) a = 0 := by
      simp [mulVec, dotProduct, vecMulVec_apply, ← Finset.mul_sum, hsum]
    rw [this, sub_zero]
  rw [tot_eq, tot_eq]
  calc (fun _ => (1 : ℂ)) ⬝ᵥ (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k *ᵥ fun _ => 1)
      = (fun _ => (1 : ℂ)) ⬝ᵥ (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k *ᵥ (Q *ᵥ fun _ => 1)) := by rw [hr]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k * Q) *ᵥ fun _ => 1) := by
        rw [mulVec_mulVec]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Q * Formalism.REAL.Amat l ^ k) *ᵥ fun _ => 1) := by rw [hk.eq]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ (Q *ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1)) := by rw [mulVec_mulVec]
    _ = ((fun _ => (1 : ℂ)) ᵥ* Q) ⬝ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1) := dotProduct_mulVec _ _ _
    _ = _ := by rw [hl]

theorem tot_swap {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (k : ℕ) :
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  by_cases hd : l p - l q - 1 = 0
  · have hne : p ≠ q := by intro h; rw [h] at hpq; omega
    have hd' : (l ∘ Equiv.swap p q) p - (l ∘ Equiv.swap p q) q - 1 ≠ 0 := by
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      intro h; apply two_ne_zero (α := ℂ); linear_combination -h - hd
    have := tot_swap_of (l ∘ Equiv.swap p q) p q hpq hd' k
    have hinv : (l ∘ Equiv.swap p q) ∘ Equiv.swap p q = l := by
      funext a; simp [Equiv.swap_apply_self]
    rw [hinv] at this
    exact this.symm
  · exact tot_swap_of l p q hpq hd k

theorem tot_perm {n : ℕ} (s : Equiv.Perm (Fin n)) : ∀ (l : Fin n → ℂ) (k : ℕ),
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ s) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  cases n with
  | zero =>
    have : s = 1 := Subsingleton.elim _ _
    subst this; intro l k; rfl
  | succ m =>
    have hs : s ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; trivial
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro l k
      exact tot_swap l i.castSucc i.succ (by simp) k
    | one => intro l k; rfl
    | mul x y _ _ hx hy =>
      intro l k
      have hc : l ∘ ⇑(x * y) = (l ∘ ⇑x) ∘ ⇑y := by ext c; simp
      rw [hc, hy (l ∘ ⇑x) k, hx l k]

theorem gelfVal_shift_symm : ∀ (n : ℕ) (χ : Fin n → ℂ), (∀ (t : ℂ) (k : ℕ), gelfVal (fun a => χ a + t) k = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * t ^ (k - j) * gelfVal χ j) ∧ gelfVal χ 0 = n ∧ ∀ (s : Equiv.Perm (Fin n)) (k : ℕ), gelfVal (χ ∘ s) k = gelfVal χ k := by
  intro n χ
  refine ⟨?_, ?_, ?_⟩
  · intro t k
    unfold gelfVal
    have e : (fun c => χ c + t + ((n : ℂ) - 1) / 2) = fun c => (χ c + ((n : ℂ) - 1) / 2) + t := by
      funext c; ring
    set A := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2)
    have hM : (A + t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k =
        ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * t ^ (k - j)) • A ^ j := by
      rw [(Commute.smul_right (Commute.one_right A) t).add_pow]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, one_pow, Matrix.mul_smul, mul_one, ← Nat.cast_comm, ← nsmul_eq_mul,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [e, amat_add_const, hM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := range (k + 1))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_comm
  · simp [gelfVal, Matrix.one_apply]
  · intro s k
    unfold gelfVal
    have e : (fun c => (χ ∘ s) c + ((n : ℂ) - 1) / 2) = (fun c => χ c + ((n : ℂ) - 1) / 2) ∘ s := rfl
    rw [e, tot_perm]

end GlobalTheory.GelfValSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraCentralAction
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUCentre

lemma card_lt_add_card_gt {n : ℕ} (lam : Fin n → ℝ) (hinj : Function.Injective lam) (a : Fin n) :
    ((univ.filter fun b => lam b < lam a).card : ℝ) + ((univ.filter fun b => lam a < lam b).card : ℝ) + 1 = n := by
  have h1 : (univ.filter fun b => lam b ≠ lam a) = univ.erase a := by
    ext b; simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact ⟨fun h e => h (e ▸ rfl), fun h e => h (hinj e)⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b => lam b ≠ lam a)
    (fun b => lam b < lam a)
  have h3 : ((univ.filter fun b => lam b ≠ lam a).filter fun b => lam b < lam a) = univ.filter fun b => lam b < lam a := by
    ext b; simp only [mem_filter, mem_univ, true_and]; exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  have h4 : ((univ.filter fun b => lam b ≠ lam a).filter fun b => ¬ lam b < lam a) = univ.filter fun b => lam a < lam b := by
    ext b; simp only [mem_filter, mem_univ, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨h.ne', h.le⟩⟩
  rw [h3, h4, h1, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin] at h2
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ a).elim0)
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [← h2] at this
  push_cast at this
  linarith

lemma card_split {n : ℕ} (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    ((univ.filter fun b => P b ∧ Q b).card : ℝ) + ((univ.filter fun b => P b ∧ ¬ Q b).card : ℝ) =
      ((univ.filter P).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := univ.filter P) Q
  rw [Finset.filter_filter, Finset.filter_filter] at h
  exact_mod_cast h

lemma lowCh_shift_int {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsParU lam) (c : ℝ) (a : Fin n) :
    ∃ k : ℤ, lowCh ε (fun b => lam b - c) a = (k : ℝ) - c := by
  obtain ⟨m0, hm0⟩ := hlam.2 a
  have hN : rhoNh ε (fun b => lam b - c) a = rhoNh ε lam a := by
    simp only [rhoNh, sub_lt_sub_iff_right]
  have hC : rhoCh ε (fun b => lam b - c) a = rhoCh ε lam a := by
    simp only [rhoCh, sub_lt_sub_iff_right]
  have hsum := card_lt_add_card_gt lam hlam.1 a
  have s1 := card_split (fun b => lam b < lam a) (fun b => ε b = ε a)
  have s2 := card_split (fun b => lam a < lam b) (fun b => ε b = ε a)
  refine ⟨m0 + ((univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card : ℤ)
    + ((univ.filter fun b => lam a < lam b ∧ ε b = ε a).card : ℤ), ?_⟩
  have e : lowCh ε (fun b => lam b - c) a
      = lam a - c + rhoNh ε (fun b => lam b - c) a - rhoCh ε (fun b => lam b - c) a := rfl
  rw [e, hN, hC]
  simp only [rhoNh, rhoCh]
  push_cast
  simp only [ne_eq] at *
  linarith

lemma scalar_as_torus {n : ℕ} (a0 : Fin n) (z : ℂ) (hz : z ^ n = 1) :
    ∃ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) = z ∧
      ∑ a, (if a = a0 then t - n * t else t) = 0 ∧
      z • (1 : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun a => Complex.exp ((((if a = a0 then t - n * t else t : ℝ)) : ℂ) * Complex.I)) := by
  have hn : n ≠ 0 := fun h => (h ▸ a0).elim0
  have hnorm : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp this
  set t := Complex.arg z
  have ht : Complex.exp ((t : ℂ) * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hnorm] at this; simpa using this
  have ht' : Complex.exp (((t - n * t : ℝ) : ℂ) * Complex.I) = z := by
    push_cast
    rw [sub_mul, Complex.exp_sub, mul_assoc, Complex.exp_nat_mul, ht, hz, div_one]
  refine ⟨t, ht, ?_, ?_⟩
  · have e : ∀ a : Fin n, (if a = a0 then t - n * t else t) = t - (if a = a0 then n * t else 0) := by
      intro a; split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h0 : i = a0
      · simp only [h0, diagonal_apply_eq, if_true, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]; exact ht'.symm
      · simp [h0, ht]
    · simp [hij]

theorem centre_acts : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (m : ℤ), IsParU lam → ∑ a, lam a = (m : ℝ) →
    IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∀ z : ℂ, z ^ n = 1 → ∀ v,
    π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v := by
  intro n hn ε H _ _ π' lam m hpar hsum hHC z hz v
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  let a0 : Fin n := ⟨0, hn⟩
  obtain ⟨t, ht, hθsum, hdiag⟩ := scalar_as_torus a0 z hz
  obtain ⟨hirr, _, ⟨S0, hS0, _⟩, _⟩ := hHC
  obtain ⟨hΛsum, _, _, _, ⟨v0, _, hv0, hwt⟩, _⟩ := hS0
  obtain ⟨k, hk⟩ := lowCh_shift_int ε lam hpar ((m : ℝ) / n) a0
  set Λ := lowCh ε (fun a => lam a - (m : ℝ) / n)

  have hscal : ∑ a, Λ a * (if a = a0 then t - n * t else t) = -(n : ℝ) * t * k + t * m := by
    have e : ∀ a : Fin n, Λ a * (if a = a0 then t - n * t else t) = Λ a * t - (if a = a0 then Λ a0 * (n * t) else 0) := by
      intro a; split_ifs with h
      · subst h; ring
      · ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, if_true, ← Finset.sum_mul, hΛsum, zero_mul]
    rw [hk]; field_simp; ring
  have key : π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 = z ^ m • v0 := by
    rw [hdiag, hwt _ hθsum, hscal]
    congr 1
    have e2 : (((-(n : ℝ) * t * k + t * m : ℝ)) : ℂ) * Complex.I
        = ((-((n : ℤ) * k) : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((m : ℤ) : ℂ) * ((t : ℂ) * Complex.I) := by
      push_cast; ring
    rw [e2, Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, ht, _root_.zpow_neg, _root_.zpow_mul, zpow_natCast, hz,
      _root_.one_zpow, inv_one, one_mul]

  have hnorm : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).mp this
  have hzSU : z • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
    refine ⟨?_, ?_⟩
    · show (z • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * Jm ε * (z • 1) = Jm ε
      have hc : z * star z = 1 := by
        rw [Complex.star_def, Complex.mul_conj', hnorm]; simp
      rw [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, hc, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, det_one, mul_one, hz]
  have hrep := hirr.2.2.1.1.2
  set f : H →L[ℂ] H := π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) - z ^ m • ContinuousLinearMap.id ℂ H
  have hmem : ∀ w, w ∈ LinearMap.ker (f : H →ₗ[ℂ] H) ↔ π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) w = z ^ m • w := by
    intro w
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, f, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  have hclosed : IsClosed ((LinearMap.ker (f : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := ContinuousLinearMap.isClosed_ker f
  have hstab : ∀ g ∈ SUset ε, ∀ w ∈ LinearMap.ker (f : H →ₗ[ℂ] H), π' g w ∈ LinearMap.ker (f : H →ₗ[ℂ] H) := by
    intro g hg w hw
    rw [hmem] at hw ⊢
    have hcomm : z • (1 : Matrix (Fin n) (Fin n) ℂ) * g = g * (z • 1) := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have h1 := hrep _ hzSU g hg
    have h2 := hrep g hg _ hzSU
    rw [hcomm] at h1
    calc π' (z • 1) (π' g w) = ((π' (z • 1)).comp (π' g)) w := rfl
      _ = (π' g) (π' (z • 1) w) := by rw [← h1, h2]; rfl
      _ = z ^ m • π' g w := by rw [hw, map_smul]
  rcases hirr.2.2.2.1 (LinearMap.ker (f : H →ₗ[ℂ] H)) hclosed hstab with h | h
  · exact absurd (by rw [← Submodule.mem_bot ℂ, ← h, hmem]; exact key) hv0
  · exact (hmem v).mp (h ▸ Submodule.mem_top)

end GlobalTheory.SUCentre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_discreteSeries_unipotent_vanishes : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.RealFibre.integral_phe_eq_zero | exact GlobalTheory.RealFibre.integral_phe_eq_zero | (intros; apply GlobalTheory.RealFibre.integral_phe_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermsSameDoubleCosetSameDatumStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTerms_same_doubleCoset_same_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (t₁ t₂ : Term V M r), H.IsTerm t₁ → H.IsTerm t₂ → t₂.abelian₂ = t₁.abelian₂ → t₂.T = t₁.T → t₂.T' = t₁.T' → ∀ n ∈ NU H t₁.f, ∀ m ∈ NU H t₁.f', img (n * m) t₁.abelian₂ = t₁.abelian₂ → Tri E t₁.f t₂.f → Tri E (fun b => (n * m) (t₁.f' b)) t₂.f' → (M.split ≠ none → ∀ x' ∈ t₁.abelian₂, ∀ x ∈ t₁.abelian₂, x' ∈ H.perp (H.X t₁.f') → x ∈ H.perp (H.X t₁.f) → (Cong H t₁.abelian₂ t₁.f t₁.f' (x - x') ↔ Cong H t₁.abelian₂ t₂.f t₂.f' (x - (n * m) x'))) → ∀ d : Datum P, Over P d t₁ → Over P d t₂ := by
  first | exact @GlobalTheory.LocOver.SameDC.same_datum | exact GlobalTheory.LocOver.SameDC.same_datum | (intros; apply GlobalTheory.LocOver.SameDC.same_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixUnitDerivEqTraceFreeAddDegree
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CentralLetter

variable {n : ℕ}

theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = Complex.exp c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem inG_imag (ε : Fin n → Bool) (s : ℝ) :
    inG ε (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold inG
  simp [Matrix.conjTranspose_smul]

theorem Rd_central (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hG : ∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x)
    (s : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) (hx : inUJ ε x) :
    Rd (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) G x = (m : ℂ) * (s * Complex.I) * G x := by
  unfold Rd
  have h1 : (fun t : ℝ => G (x * NormedSpace.exp ((t : ℂ) • (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)))))
      = fun t : ℝ => Complex.exp ((t : ℂ) * ((m : ℂ) * (s * Complex.I))) * G x := by
    funext t
    rw [smul_smul, exp_smul_one, Matrix.mul_smul, Matrix.mul_one, hG _ _ x hx, ← Complex.exp_int_mul]
    · congr 2; ring
    · rw [← mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [h1]
  have h2 : HasDerivAt (fun t : ℂ => Complex.exp (t * ((m : ℂ) * (s * Complex.I))) * G x)
      ((m : ℂ) * (s * Complex.I) * G x) ((0 : ℝ) : ℂ) := by
    have := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const ((m : ℂ) * (s * Complex.I))).cexp).mul_const (G x)
    simpa using this
  exact h2.comp_ofReal.deriv

theorem cpart1_add_real (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    cpart1 ε (Z + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = cpart1 ε Z := by
  unfold cpart1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Jm_mul_self, Complex.star_def, Complex.conj_ofReal]
  congr 1
  abel

theorem cpart2_add_real (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    cpart2 ε (Z + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      cpart2 ε Z + ((((-r : ℝ)) : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold cpart2
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Jm_mul_self, Complex.star_def, Complex.conj_ofReal,
    add_add_add_comm, smul_add, ← add_smul, smul_smul]
  congr 2
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε G → (∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x) → ∀ (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ), inUJ ε x → Eab ε a b G x = Ec ε (E0 a b) G x + (if a = b then (m : ℂ) / n else 0) * G x := by
  intro n _ ε m G hs hG a b x hx
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = (if a = b then (n : ℂ)⁻¹ else 0) :=
    ⟨if a = b then (n : ℝ)⁻¹ else 0, by split_ifs <;> simp⟩
  have e : (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) = E0 a b + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hr, E0, sub_add_cancel]
  have hm : (if a = b then (m : ℂ) / n else 0) = m * r := by
    rw [hr]; split_ifs <;> simp [div_eq_mul_inv]
  unfold Eab
  rw [e, hm]
  unfold Ec
  rw [cpart1_add_real, cpart2_add_real,
    (right_derivative_linear n ε G G _ _ 0 0 x hs hs (complex_parts_mem_lie_algebra_holds n ε (E0 a b)).2.1 (inG_imag ε (-r)) hx).1,
    Rd_central ε m G hG (-r) x hx]
  push_cast
  linear_combination (-(m : ℂ) * r * G x) * Complex.I_sq

end GlobalTheory.CentralLetter

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLevelOfPreservesFirstComponentsSplitStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_preserves_first_components_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  first | exact @GlobalTheory.St.G.mem_levelVL_of_first_components | exact GlobalTheory.St.G.mem_levelVL_of_first_components | (intros; apply GlobalTheory.St.G.mem_levelVL_of_first_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotientStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_identity_besselCoefficient_quotient : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) ∧ Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν ∧ MemLp (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) 2 ν ∧ ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν = ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) ∧ 0 ≤ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).re ∧ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).im = 0 := by
  first | exact @GlobalTheory.SgInf.normIdentity_besselCoef | exact GlobalTheory.SgInf.normIdentity_besselCoef | (intros; apply GlobalTheory.SgInf.normIdentity_besselCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowthStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ → ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R → μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)
end


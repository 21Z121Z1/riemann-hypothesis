import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnits
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
section
open Formalism.MainNotions

namespace GlobalTheory.ResidueRoot

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : ℂ_[p])‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : ℂ_[p])‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rw [norm_neg]; exact ha

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_add_lt_one {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem sub_one_lt_of_pow_p {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p - 1‖ < 1) : ‖y - 1‖ < 1 := by
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (Y - 1) 1
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p = (y ^ p - 1) + -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this] at hr'
    rw [hr']; ring
  have h2 : ‖(y - 1) ^ p‖ < 1 := by
    rw [e]
    refine norm_add_lt_one h ?_
    rw [norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h2

theorem sub_one_lt_of_pow_p_pow (k : ℕ) {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p ^ k - 1‖ < 1) :
    ‖y - 1‖ < 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply sub_one_lt_of_pow_p
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    · rwa [← pow_mul, ← pow_succ]

theorem exists_root {x : ℂ_[p]} {m : ℕ} (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[p], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_pow_alg (x : PadicAlgCl p) (hx : ‖x‖ = 1) : ∃ n, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | (apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one ..)

end GlobalTheory.ResidueRoot

namespace GlobalTheory

open ResidueRoot

theorem exists_mem_Wp_norm_sub_lt_one (p : ℕ) [hp : Fact p.Prime] (x : ℂ_[p]) (hx : ‖x‖ ≤ 1) :
    ∃ w ∈ GL3Theta.Wp p, ‖x - w‖ < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖(y : ℂ_[p])‖ ≤ 1 := by
    have : (y : ℂ_[p]) = x + -(x - y) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  rcases hy1.lt_or_eq with h | h
  · refine ⟨0, zero_mem _, ?_⟩
    have := norm_add_lt_one hy h
    simpa using this
  · obtain ⟨n, hn, hyn⟩ := exists_pow_alg y (by rwa [PadicComplex.norm_extends] at h)
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
    have h3 : ‖((y : ℂ_[p]) ^ m) ^ p ^ k - 1‖ < 1 := by
      rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
        ← PadicComplex.coe_eq] at hyn
      rwa [← pow_mul, mul_comm]
    have h4 := sub_one_lt_of_pow_p_pow k
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1) h3
    obtain ⟨ζ, hζ, h5⟩ := exists_root hm0 h4
    refine ⟨ζ, Subring.le_topologicalClosure _ (Subring.subset_closure
      ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm, hζ⟩), ?_⟩
    have := norm_add_lt_one hy h5
    simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroMapEqZeroOfWeightNe
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowDiv_eq_zero_of_unipotent_fixed {n : ℕ} (nu : DomWeight n) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → sqAct ℂ n nu g q = q)
    (a b : Fin n) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℂ a b k q = 0 := by
  have hfix : ∀ t : ℂ, rowAct ℂ (lfockq_mat a b t) q = q := by
    intro t
    have htri : (lfockq_mat a b t).transpose.BlockTriangular id := by
      intro i j hij
      have hij' : j < i := hij
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_neg hij'.ne, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hij'
    have hdiag : ∀ i, (lfockq_mat a b t).transpose i i = 1 := by
      intro i
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_pos trivial, if_neg, add_zero]
      rintro ⟨h1, h2⟩
      exact hab.ne (h2.symm.trans h1)
    have hdet : (lfockq_mat a b t).transpose.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp only [hdiag, Finset.prod_const_one]
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero :
      (lfockq_mat a b t).transpose.det ≠ 0)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = (lfockq_mat a b t).transpose := rfl
    have hd : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hdet, Units.val_one]
    have := hq g htri hdiag
    unfold sqAct at this
    rwa [detPow, hd, one_zpow, Units.val_one, one_smul, hg, Matrix.transpose_transpose] at this
  have hP : rowGen ℂ a b q = Polynomial.C q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (C_injective (Fin n × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [lfockq_eval_rowGen, hfix, Polynomial.eval_C]
  rw [rowDiv, hP, Polynomial.coeff_C, if_neg (by omega)]

theorem exists_ne_zero_map_eq_zero_of_weight_ne (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (sqRep ℂ n mu).IntertwiningMap (sqRep ℂ n nu)) :
    ∃ f : nablaSq ℂ n mu, f ≠ 0 ∧ φ f = 0 := by
  let f : nablaSq ℂ n mu := ⟨extremal ℂ n mu, hwMem ℂ n n le_rfl _ (factNatW n mu).1⟩
  refine ⟨f, fun h => hwNe ℂ n n le_rfl mu.natW (congrArg Subtype.val h), ?_⟩
  have hint : ∀ g x, φ (sqRep ℂ n mu g x) = sqRep ℂ n nu g (φ x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (φ f : MvPolynomial (Fin n × Fin n) ℂ) = c • extremal ℂ n nu := by
    apply hwLine ℂ n n le_rfl nu.natW (factNatW n nu).1 _ (φ f).2
    intro a b hab k hk
    refine rowDiv_eq_zero_of_unipotent_fixed nu _ (fun g h1 h2 => ?_) a b hab k hk
    have e : sqRep ℂ n mu g f = f := Subtype.ext ((factSqHighestWeight ℂ n mu).2 g h1 h2)
    rw [← sqRep_coe, ← hint, e]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ nu.w i := by
    by_contra h
    push Not at h
    apply hne
    obtain ⟨w, hw⟩ := mu
    obtain ⟨w', hw'⟩ := nu
    have : w = w' := funext h
    subst this
    rfl
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  let t : Fin n → ℂˣ := fun a => if a = i then u else 1
  have hprod : ∀ lam : DomWeight n, ((∏ a, (t a) ^ (lam.w a) : ℂˣ) : ℂ) = (2 : ℂ) ^ lam.w i := by
    intro lam
    rw [Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)]
    simp [t, u]
  have e : sqRep ℂ n mu (diagGL ℂ n t) f = (2 : ℂ) ^ mu.w i • f := by
    apply Subtype.ext
    rw [← hprod]
    exact (factSqHighestWeight ℂ n mu).1 t
  have e2 : sqRep ℂ n nu (diagGL ℂ n t) (φ f) = (2 : ℂ) ^ nu.w i • φ f := by
    let h : nablaSq ℂ n nu := ⟨extremal ℂ n nu, hwMem ℂ n n le_rfl _ (factNatW n nu).1⟩
    have hc' : φ f = c • h := Subtype.ext hc
    have e3 : sqRep ℂ n nu (diagGL ℂ n t) h = (2 : ℂ) ^ nu.w i • h := by
      apply Subtype.ext
      rw [← hprod]
      exact (factSqHighestWeight ℂ n nu).1 t
    rw [hc', map_smul, e3, smul_comm]
  have e4 := hint (diagGL ℂ n t) f
  rw [e, e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e4
  refine e4.resolve_left fun h => hi ?_
  have h' : ((2 : ℝ) ^ mu.w i) = (2 : ℝ) ^ nu.w i := by
    simpa [norm_zpow] using congrArg norm h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h'

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSsIdxInjective
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

noncomputable section

namespace GlobalTheory.Branching.SsInj

def ps {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : ℕ) (t : Fin k) : ℕ :=
  ∑ b : Fin r, if b.val < a then m (b, t) else 0

theorem interlaced_iff {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) :
    Interlaced m ↔ ∀ l j : Fin k, j.val = l.val + 1 → ∀ a : Fin r, ps m (a.val + 1) j ≤ ps m a.val l := by
  simp only [Interlaced, InterlacedAt, ps, Finset.sum_filter, zero_add, Nat.lt_succ_iff, Fin.le_def, Fin.lt_def]

theorem ps_zero {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m 0 t = 0 := by simp [ps]

theorem ps_succ {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : Fin r) (t : Fin k) :
    ps m (a.val + 1) t = ps m a.val t + m (a, t) := by
  have : m (a, t) = ∑ b : Fin r, if b = a then m (b, t) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b = a
  · subst h; simp
  · have h' : b.val ≠ a.val := fun e => h (Fin.ext e)
    rw [if_neg h]
    split_ifs <;> omega

theorem ps_top {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m r t = ∑ b, m (b, t) := by
  simp [ps]

theorem ps_diag {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    ∀ (t : ℕ) (ht : t < r), ps m t ⟨t, ht⟩ = 0
  | 0, _ => ps_zero m _
  | t + 1, ht => by
    have h1 := (interlaced_iff m).1 hm ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl ⟨t, by omega⟩
    have h2 := ps_diag m hm t (by omega)
    simp only at h1
    omega

theorem diag_anti {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    Antitone fun t : Fin r => m (t, t) := by
  cases r with
  | zero => intro a; exact a.elim0
  | succ r =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h1 := (interlaced_iff m).1 hm i.castSucc i.succ (by simp) i.succ
    have h2 := ps_succ m i.succ i.succ
    have h3 := ps_succ m i.castSucc i.castSucc
    have h4 : ps m i.succ.val i.succ = 0 := ps_diag m hm _ i.succ.2
    have h5 : ps m i.castSucc.val i.castSucc = 0 := ps_diag m hm _ i.castSucc.2
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega

def res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m (v.1.castSucc, v.2.castSucc)

theorem res_apply {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a t : Fin n) :
    res m (a, t) = m (a.castSucc, t.castSucc) := rfl

theorem ps_res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a : ℕ) (ha : a ≤ n) (t : Fin n) :
    ps (res m) a t = ps m a t.castSucc := by
  have : ¬ n < a := by omega
  simp [ps, Fin.sum_univ_castSucc, res_apply, this]

theorem res_interlaced {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : Interlaced m) :
    Interlaced (res m) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  rw [ps_res _ _ (by omega), ps_res _ _ (by omega)]
  exact hm l.castSucc j.castSucc hj a.castSucc

def subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m v - if v.1 = v.2 then c else 0

theorem subDiag_add {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a t : Fin n) :
    subDiag m c (a, t) + (if a = t then c else 0) = m (a, t) := by
  have e : subDiag m c (a, t) = m (a, t) - if a = t then c else 0 := rfl
  rw [e]
  split_ifs with h
  · subst h
    have := hc a
    omega
  · simp

theorem ps_subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a : ℕ) (t : Fin n) :
    ps (subDiag m c) a t + (if t.val < a then c else 0) = ps m a t := by
  have : (if t.val < a then c else 0) = ∑ b : Fin n, if b = t then (if t.val < a then c else 0) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := subDiag_add m c hc b t
  by_cases h : b = t
  · subst h
    simp only [if_true] at this ⊢
    split_ifs <;> omega
  · simp only [if_neg h] at this ⊢
    split_ifs <;> omega

theorem subDiag_interlaced {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t))
    (hm : Interlaced m) : Interlaced (subDiag m c) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  have h1 := hm l j hj a
  have h2 := ps_subDiag m c hc (a.val + 1) j
  have h3 := ps_subDiag m c hc a.val l
  split_ifs at h2 h3 <;> omega

theorem natW_cast {N : ℕ} (lam : DomWeight N) (t : Fin N) :
    (lam.natW t : ℤ) = lam.w t - lam.detShift := by
  have h0 : 0 < N := t.pos
  have := lam.anti (show t ≤ ⟨N - 1, by omega⟩ from Fin.le_def.2 (by have := t.2; simp only; omega))
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos h0]
  omega

theorem exists_image (n : ℕ) (lam : DomWeight (n + 1)) (m : ssIdx (n + 1) (n + 1) lam.natW) :
    ∃ x : (Σ mu : Below rfl lam, ssIdx n n mu.1.natW),
      (∀ t, x.1.1.w t = lam.detShift + ps m.1 n t.castSucc) ∧
      ∀ a t, x.2.1 (a, t) + (if a = t then (x.1.1.detShift - lam.detShift).toNat else 0) =
        m.1 (a.castSucc, t.castSucc) := by
  obtain ⟨m, hm, hcol⟩ := m
  have hup : ∀ t : Fin n, lam.detShift + ps m n t.castSucc ≤ lam.w t.castSucc := fun t => by
    have h1 := ps_succ m (Fin.last n) t.castSucc
    have h2 := ps_top m t.castSucc
    have h3 := hcol t.castSucc
    have h4 := natW_cast lam t.castSucc
    simp only [Fin.val_last] at h1
    omega
  have hlo : ∀ t : Fin n, lam.w t.succ ≤ lam.detShift + ps m n t.castSucc := fun t => by
    have h1 := (interlaced_iff m).1 hm t.castSucc t.succ (by simp) (Fin.last n)
    have h2 := ps_top m t.succ
    have h3 := hcol t.succ
    have h4 := natW_cast lam t.succ
    simp only [Fin.val_last] at h1
    omega
  let mu : DomWeight n := ⟨fun t => lam.detShift + ps m n t.castSucc, fun i j hij => by
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hup j).trans ((lam.anti (Fin.le_def.2 (by simpa using hlt))).trans (hlo i))⟩
  have hI : Interlace rfl lam mu := fun i => ⟨hup i, hlo i⟩
  have hr := res_interlaced m hm
  have hc' : ∀ h0 : 0 < n, mu.detShift - lam.detShift =
      (res m (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) : ℕ) := fun h0 => by
    have h1 := ps_succ (res m) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
    have h2 := ps_diag (res m) hr (n - 1) (by omega)
    have h3 := ps_res m n le_rfl ⟨n - 1, by omega⟩
    have h4 : mu.detShift = lam.detShift + ps m n (Fin.castSucc ⟨n - 1, by omega⟩) := by
      simp only [DomWeight.detShift, dif_pos h0, mu]
    have h5 : n - 1 + 1 = n := by omega
    simp only [h5] at h1
    omega
  have hc : ∀ t, (mu.detShift - lam.detShift).toNat ≤ res m (t, t) := fun t => by
    have h0 : 0 < n := t.pos
    rw [hc' h0, Int.toNat_natCast]
    exact diag_anti _ hr (Fin.le_def.2 (by have := t.2; simp only; omega))
  refine ⟨⟨⟨mu, hI⟩, subDiag (res m) _, subDiag_interlaced _ _ hc hr, fun t => ?_⟩, fun _ => rfl,
    fun a t => subDiag_add _ _ hc a t⟩
  have h1 := ps_subDiag _ _ hc n t
  rw [if_pos t.2, ps_top, ps_res m n le_rfl] at h1
  have h2 := natW_cast mu t
  have h3 : mu.w t = lam.detShift + ps m n t.castSucc := rfl
  have h4 := hc' t.pos
  simp only
  omega

end GlobalTheory.Branching.SsInj

namespace GlobalTheory.Branching

open SsInj

theorem exists_ssIdx_injective : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    ∃ F : ssIdx N N lam.natW → (Σ mu : Below h lam, ssIdx n n mu.1.natW), Function.Injective F := by
  intro n N h lam
  subst h
  choose F hF1 hF2 using exists_image n lam
  refine ⟨F, fun m m' e => ?_⟩
  have hin : ∀ a t : Fin n, m.1 (a.castSucc, t.castSucc) = m'.1 (a.castSucc, t.castSucc) := fun a t => by
    rw [← hF2 m a t, ← hF2 m' a t, e]
  have hlast : ∀ x : ssIdx (n + 1) (n + 1) lam.natW, ∀ a, x.1 (a, Fin.last n) = 0 := fun x a => by
    have h1 := x.2.2 (Fin.last n)
    have h2 : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, Fin.last]
    rw [h2] at h1
    exact Finset.sum_eq_zero_iff.1 h1 a (Finset.mem_univ a)
  apply Subtype.ext
  ext ⟨a, t⟩
  induction t using Fin.lastCases with
  | last => rw [hlast, hlast]
  | cast t =>
    induction a using Fin.lastCases with
    | cast a => exact hin a t
    | last =>
      have h1 := m.2.2 t.castSucc
      have h2 := m'.2.2 t.castSucc
      rw [Fin.sum_univ_castSucc] at h1 h2
      simp only [hin] at h1
      omega

end GlobalTheory.Branching
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_genericDet (R : Type) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (lpMinor R n le_rfl le_rfl) = C g.det * lpMinor R n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 p q
  simp [rowAct, Matrix.mul_apply]

theorem genericDet_pow_mem (R : Type) [CommRing R] (n c : ℕ) :
    lpMinor R n le_rfl le_rfl ^ c ∈ dualWeyl R n n (fun _ => c) := by
  have h := bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)
  have e : shapeDeg (n := n) (fun _ : Fin c => n) = fun _ => c := by
    funext t
    simp [shapeDeg]
  rw [e] at h
  simpa [bideterminant, initMinor, lpMinor] using h

theorem genericDet_pow_mul_hw (R : Type) [CommRing R] (n c : ℕ) (ν : Fin n → ℕ) :
    lpMinor R n le_rfl le_rfl ^ c * hw R le_rfl ν = hw R (le_refl n) (fun i => ν i + c) := by
  cases n with
  | zero => simp [hw, lpMinor]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have hs : (Fin.castSucc s).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_pos hs]
      omega
    · have hs : ¬ (Fin.last m).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_neg hs, Nat.sub_zero]
      rw [pow_add, mul_comm]
      rfl

theorem genericDet_pow_mul :
    ∀ (n c : ℕ) (ν : Fin n → ℕ), (∀ f ∈ dualWeyl ℂ n n ν, lpMinor ℂ n le_rfl le_rfl ^ c * f ∈ dualWeyl ℂ n n (fun i => ν i + c)) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ), rowAct ℂ g (lpMinor ℂ n le_rfl le_rfl ^ c * f) = g.det ^ c • (lpMinor ℂ n le_rfl le_rfl ^ c * rowAct ℂ g f)) ∧ (Antitone ν → lpMinor ℂ n le_rfl le_rfl ^ c * hw ℂ le_rfl ν = hw ℂ (le_refl n) (fun i => ν i + c)) := by
  intro n c ν
  refine ⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩
  · rw [mul_comm]
    exact (dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)
  · rw [map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnitsStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → ∀ f : X.K, Inv X (CongruenceSubgroup.Gamma M) f → f ∈ IntermediateField.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}) := by
  first | exact @GlobalTheory.KZ.FracGen.fracGen | exact GlobalTheory.KZ.FracGen.fracGen | (intros; apply GlobalTheory.KZ.FracGen.fracGen <;> assumption)
end


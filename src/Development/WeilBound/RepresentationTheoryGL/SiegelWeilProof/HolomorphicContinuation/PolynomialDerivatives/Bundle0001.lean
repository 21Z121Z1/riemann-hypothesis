import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.OneMom

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HasFDerivAtEvX
section
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1))
  else (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1)

theorem crd_apply (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    crd k x = if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [Complex.conjCLE_apply, Complex.star_def]

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

theorem norm_crd_le (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ‖crd k x‖ ≤ ‖x‖ := by
  rw [crd_apply]
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  split_ifs <;> simpa using h

def dP (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ := ∑ k, evX (pderiv k P) x • crd k

theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (fun y => evX P y) (dP P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : dP (C a : PX m n) x = 0 := by simp [dP, evX_eq]
    have e : (fun y => evX (C a : PX m n) y) = fun _ => a := by funext y; simp [evX_eq]
    rw [this, e]; exact hasFDerivAt_const a x
  | add p q hp hq =>
    have : dP (p + q) x = dP p x + dP q x := by simp [dP, evX_eq, Finset.sum_add_distrib, add_smul]
    have e : (fun y => evX (p + q) y) = fun y => evX p y + evX q y := by funext y; simp [evX_eq]
    rw [this, e]; exact hp.add hq
  | mul_X p k hp =>
    have h1 : HasFDerivAt (fun y => evX p y * crd k y) (evX p x • crd k + crd k x • dP p x) x :=
      hp.mul (crd k).hasFDerivAt
    have e1 : (fun y => evX (p * X k) y) = fun y => evX p y * crd k y := by
      funext y; simp [evX_eq]
    have e2 : dP (p * X k) x = evX p x • crd k + crd k x • dP p x := by
      ext v
      have hb : ∀ b, evX (pderiv b (p * X k)) x * crd b v =
          crd k x * (evX (pderiv b p) x * crd b v) + (if k = b then evX p x * crd k v else 0) := by
        intro b
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : k = b
        · subst h; simp [evX_eq]; ring
        · simp [evX_eq, Pi.single_apply, Ne.symm h, h]; ring
      simp only [dP, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        ← Finset.mul_sum]
      ring
    rw [e1, e2]; exact h1

end PositivityTheory.Rg.Sw.LC.NullS
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HopPderivComm
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem hop_pderiv_comm' (i j : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (R := ℂ) i (pderiv (R := ℂ) j p) = pderiv (R := ℂ) j (pderiv (R := ℂ) i p) := by
  have h : (⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ : Derivation ℂ (PX m n) (PX m n)) = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases h1 : j = k <;> by_cases h2 : i = k <;> simp [Pi.single_apply, h1, h2]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_false (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, false) Q = -pderiv (a, i, false) Q + (2 * c : ℂ) • (X (a, i, true) * Q) := by
  simp [cr]

theorem cr_true (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, true) Q = -pderiv (a, i, true) Q + (2 * c : ℂ) • (X (a, i, false) * Q) := by
  simp [cr]

theorem hop_fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, support_C, if_neg hr, Finset.sum_singleton, coeff_C, if_pos rfl]
    simp [fockMono, smul_eq_C_mul]

theorem hop_pderiv_cr (c : ℝ) (j k : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + C (2 * c : ℂ) * (if k = (j.1, j.2.1, !j.2.2) then Q else 0) := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, false)]
    by_cases h : k = (a, i, true)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]
  · rw [cr_true, cr_true]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, true)]
    by_cases h : k = (a, i, false)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]

theorem sgn_mul_same (ε : Fin m → Bool) {a b : Fin m} (h : ε a = ε b) : sgn ε a * sgn ε b = 1 := by
  unfold sgn; rw [h]; split_ifs <;> norm_num

theorem sgn_mul_diff (ε : Fin m → Bool) {a b : Fin m} (h : ε a ≠ ε b) : sgn ε a * sgn ε b = -1 := by
  unfold sgn
  cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem hop_cr_C_mul (c : ℝ) (j : Fin m × Fin n × Bool) (r : ℂ) (Q : PX m n) : cr c j (C r * Q) = C r * cr c j Q := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring
  · rw [cr_true, cr_true, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring

section
variable (hB : FockBasic)
include hB

def hop_fL {c : ℝ} (hc : 0 < c) : PX m n →ₗ[ℂ] PX m n := IsLinearMap.mk' (fock c) (hB m n c hc).1

theorem fL_apply {c : ℝ} (hc : 0 < c) (p : PX m n) : hop_fL hB hc p = fock c p := rfl

theorem hop_fock_X_mul {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    fock c (X k * p) = cr c k (fock c p) := (hB m n c hc).2.2 k p

theorem fock_add'' {c : ℝ} (hc : 0 < c) (p q : PX m n) : fock c (p + q) = fock c p + fock c q :=
  (hB m n c hc).1.map_add p q

theorem fock_zero' {c : ℝ} (hc : 0 < c) : fock c (0 : PX m n) = 0 := by
  rw [← fL_apply hB hc, map_zero]

theorem hop_deriv_fock {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (k.1, k.2.1, !k.2.2) (fock c p) = C (2 * c : ℂ) * fock c (pderiv k p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => rw [hop_fock_C, pderiv_C, pderiv_C, fock_zero' hB hc, mul_zero]
  | add p q hp hq =>
    rw [fock_add'' hB hc, map_add, hp, hq, map_add, fock_add'' hB hc, mul_add]
  | mul_X p j ih =>
    have hsplit : pderiv k (X j * p) = X j * pderiv k p + (if k = j then p else 0) := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
    have hcond : ((k.1, k.2.1, !k.2.2) = (j.1, j.2.1, !j.2.2)) ↔ k = j := by
      obtain ⟨a, i, e⟩ := j
      obtain ⟨b, l, e'⟩ := k
      simp [Prod.ext_iff]
    rw [mul_comm p (X j), hop_fock_X_mul hB hc, hop_pderiv_cr, ih, hsplit, fock_add'' hB hc, hop_fock_X_mul hB hc, hop_cr_C_mul]
    by_cases h : k = j
    · rw [if_pos (hcond.2 h), if_pos h]; ring
    · rw [if_neg (mt hcond.1 h), if_neg h, fock_zero' hB hc]; ring

theorem hop_tr_false {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, false) * fock c q) = fock c (X (a, i, true) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, false) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, true) q
  have h2 := hop_deriv_fock hB hc (a, i, false) q
  rw [cr_true, smul_eq_C_mul] at h1
  simp only [Bool.not_false] at h2
  rw [h1, h2]; ring

theorem hop_tr_true {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, true) * fock c q) = fock c (X (a, i, false) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, true) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, false) q
  have h2 := hop_deriv_fock hB hc (a, i, true) q
  rw [cr_false, smul_eq_C_mul] at h1
  simp only [Bool.not_true] at h2
  rw [h1, h2]; ring

theorem fockHOp_of : FockHOp := by
  intro m n ε c hc a b p
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set Y := fock c p with hY
  have d1 : ∀ i, pderiv (a, i, false) Y = C (2 * c : ℂ) * fock c (pderiv (a, i, true) p) := fun i => hop_deriv_fock hB hc (a, i, true) p
  have d2 : ∀ i, pderiv (b, i, true) Y = C (2 * c : ℂ) * fock c (pderiv (b, i, false) p) := fun i => hop_deriv_fock hB hc (b, i, false) p
  unfold hOp Dop
  rw [← fL_apply hB hc]
  by_cases h : ε a = ε b
  · rw [if_pos h, map_sum, sgn_mul_same ε h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, fL_apply, fL_apply, d1, d2]
    have e1 := hop_tr_false hB hc b i (pderiv (a, i, true) p)
    have e2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    rw [hop_pderiv_comm' (b, i, false) (a, i, true)] at e1
    simp only [sub_self, mul_zero, map_zero, zero_mul, sub_zero, map_one, one_mul]
    linear_combination e1 - e2
  · rw [if_neg h, map_sum, sgn_mul_diff ε h]
    have hab : a ≠ b := fun e => h (e ▸ rfl)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, map_smul, map_smul, fL_apply, fL_apply, d1, d2, smul_eq_C_mul, smul_eq_C_mul]
    have t2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    have t3 := hop_tr_true hB hc a i p
    have t4 := hop_tr_false hB hc b i (X (a, i, false) * p)
    have e5 : pderiv (b, i, false) (X (a, i, false) * p) = X (a, i, false) * pderiv (b, i, false) p := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      have : ((b, i, false) : Fin m × Fin n × Bool) ≠ (a, i, false) := by simp [Ne.symm hab]
      simp [Pi.single_apply, this]
    rw [e5] at t4
    rw [hop_pderiv_comm' (a, i, true) (b, i, false)] at t2
    have e6 : fock c (X (b, i, true) * (X (a, i, false) * p)) = fock c (X (a, i, false) * X (b, i, true) * p) := by
      congr 1; ring
    have hK : (C (1 / (2 * c) : ℂ) : PX m n) * C (2 * c : ℂ) = 1 := by
      rw [← map_mul, show (1 / (2 * c) : ℂ) * (2 * c) = 1 by field_simp, map_one]
    have e7 : (c : ℂ) * (1 - -1) = 2 * c := by ring
    simp only [e7, map_neg, map_one, neg_one_mul, neg_neg]
    linear_combination t2 - X (b, i, false) * t3 - C (1 / (2 * c) : ℂ) * t4 - C (1 / (2 * c) : ℂ) * e6 +
      (X (b, i, false) * fock c (X (a, i, false) * p) - fock c (X (a, i, false) * pderiv (b, i, false) p)) * hK

end

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableMonomial
section
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def flip (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

@[simp] theorem flip_flip (k : Fin m × Fin n × Bool) : flip (flip k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flip]

def g1 (c : ℝ) (p q : ℕ) : ℂ := if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

def phi (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, g1 c (s (a, i, false)) (s (a, i, true))

def fac (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) (z : ℂ) : ℂ :=
  z ^ s (a, i, false) * star z ^ s (a, i, true) * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))

theorem evX_monomial_mul_gs (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) (x : Fin m → Fin n → ℂ) :
    evX (monomial s r) x * gs c x = r * ∏ a, ∏ i, fac c s a i (x a i) := by
  have h1 : evX (monomial s r) x = r * ∏ a, ∏ i, (x a i ^ s (a, i, false) * star (x a i) ^ s (a, i, true)) := by
    rw [evX, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.prod_bool]
    simp [mul_comm]
  have h2 : gs c x = ∏ a, ∏ i, Complex.exp ((-(c * ‖x a i‖ ^ 2) : ℝ)) := by
    rw [gs, ← Complex.ofReal_neg]
    have : (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℝ) = ∑ a, ∑ i, (-(c * ‖x a i‖ ^ 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [this, Complex.ofReal_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Complex.ofReal_sum, Complex.exp_sum]
  rw [h1, h2, mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext a
  rw [← Finset.prod_mul_distrib]
  rfl

variable (hM : OneMom)

include hM in
theorem integrable_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX (monomial s r) x * gs c x) := by
  simp_rw [evX_monomial_mul_gs]
  refine Integrable.const_mul ?_ r
  exact Integrable.fintype_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))
    (fun a => Integrable.fintype_prod (f := fun i (z : ℂ) => fac c s a i z) (fun i => (hM c hc _ _).1))

include hM in
theorem mom_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    mom c (monomial s r) = r * phi c s := by
  rw [mom]
  simp_rw [evX_monomial_mul_gs]
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_volume_eq_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (z : ℂ) => fac c s a i z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (hM c hc _ _).2

include hM in
theorem integrable_evX (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s r => exact integrable_monomial hM c hc s r
  | add P Q hP hQ =>
    have : (fun x => evX (P + Q) x * gs c x) = fun x => evX P x * gs c x + evX Q x * gs c x := by
      funext x; simp [evX, add_mul]
    rw [this]; exact hP.add hQ

include hM in
theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  rw [mom, mom, mom, ← integral_add (integrable_evX hM c hc P) (integrable_evX hM c hc Q)]
  congr 1; funext x; simp [evX, add_mul]

omit hM in
theorem mom_smul (c : ℝ) (r : ℂ) (P : PX m n) : mom c (r • P) = r * mom c P := by
  rw [mom, mom, ← integral_const_mul]
  congr 1; funext x; simp [evX, mul_assoc]

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullSecKAlg
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def MomLin : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (P Q : PX m n) (r : ℂ), mom c (P + Q) = mom c P + mom c Q ∧ mom c (r • P) = r * mom c P

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PderivComm
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.FK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def sw (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

theorem sw_inj {k k' : Fin m × Fin n × Bool} : sw k = sw k' ↔ k = k' := by
  obtain ⟨a, i, b⟩ := k
  obtain ⟨a', i', b'⟩ := k'
  cases b <;> cases b' <;> simp [sw]

theorem pderiv_comm (i j : Fin m × Fin n × Bool) (P : PX m n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅(pderiv (R := ℂ) i : Derivation ℂ (PX m n) (PX m n)), pderiv (R := ℂ) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [Pi.single_apply, hi, hj]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -(pderiv k Q) + (2 * c : ℂ) • ((X (sw k) : PX m n) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, sw]

theorem pderiv_cr (c : ℝ) (k k' : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv (sw k') (cr c k Q) = cr c k (pderiv (sw k') Q) + (if k = k' then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add, map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm (sw k') k]
  by_cases h : k = k'
  · subst h; simp; ring
  · have : sw k' ≠ sw k := fun e => h (sw_inj.1 e).symm
    simp [h, this]

theorem fock_one (c : ℝ) : fock c (1 : PX m n) = 1 := by
  classical
  have h1 : (1 : PX m n) = monomial 0 1 := rfl
  unfold fock
  rw [h1, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_smul]
  simp [fockMono]

theorem fock_C (hB : FockBasic) (c : ℝ) (hc : 0 < c) (a : ℂ) : fock c (C a : PX m n) = C a := by
  have hL := (hB m n c hc).1
  rw [show (C a : PX m n) = a • 1 by rw [smul_eq_C_mul, mul_one], hL.map_smul, fock_one, smul_eq_C_mul, mul_one]

theorem der_fock (hB : FockBasic) (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (sw k) (fock c p) = (2 * c : ℂ) • fock c (pderiv k p) := by
  classical
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  induction p using MvPolynomial.induction_on with
  | C a => rw [fock_C hB c hc]; simp [hL.map_zero]
  | add p q hp hq => rw [hL.map_add, map_add, hp, hq, map_add, hL.map_add, smul_add]
  | mul_X p k0 hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, ← hX, pderiv_mul, pderiv_X, hL.map_add, smul_add]
    by_cases h : k0 = k
    · subst h
      simp only [Pi.single_eq_same, if_true, mul_comm (X k0) (pderiv k0 p)]
      rw [one_mul, add_comm]
    · simp only [Pi.single_apply, h, if_false, add_zero, zero_smul, mul_comm (X k0) (pderiv k p)]
      rw [zero_mul, hL.map_zero, smul_zero, zero_add]

theorem qp_sum (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * ((X (a, i, true) : PX m n) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem op_id (c : ℝ) (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) :
    (∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) P)) -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) P) =
    ((c : ℂ) ^ 2) • mulQ ε i j P - lapS ε c i j P - (c : ℂ) • eulH c i j P + (c : ℂ) • eulA c i j P -
      (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P := by
  classical
  have hd : (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P =
      ∑ a, (if i = j then (c : ℂ) * sgn ε a else 0) • P := by
    by_cases hij : i = j <;> simp [hij, Finset.mul_sum, Finset.sum_smul]
  rw [hd, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold mulQ lapS eulH eulA
  rw [qp_sum, Finset.sum_mul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hε : ε a
  · simp only [hε, Bool.false_eq_true, if_false, if_true, zero_sub, cr_apply, sw, Bool.not_true]
    rw [pderiv_comm (a, j, true) (a, i, false)]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring
  · simp only [hε, if_true, Bool.true_eq_false, if_false, sub_zero, cr_apply, sw, Bool.not_false]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring

theorem kopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), (X (a, i, false) : PX m n) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), (X (a, j, true) : PX m n) * pderiv (a, i, true) p := by
  simp [KopL]

end PositivityTheory.Rg.Sw.LC.FK

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.FK

theorem fockK_of (hB : FockBasic) : FockK := by
  intro m n ε c hc
  have hc2 : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  refine ⟨(2 * c : ℂ)⁻¹ * (c : ℂ) ^ 2, -(2 * c : ℂ)⁻¹, -((2 * c : ℂ)⁻¹ * c), (2 * c : ℂ)⁻¹ * c,
    -((2 * c : ℂ)⁻¹ * ((c : ℂ) * ∑ a, sgn ε a)), fun i j p => ?_⟩
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  let L : PX m n →ₗ[ℂ] PX m n := hL.mk' (fock c)
  have eL : ∀ x, fock c x = L x := fun x => rfl
  have hd : ∀ k (q : PX m n), fock c (pderiv k q) = (2 * c : ℂ)⁻¹ • pderiv (sw k) (fock c q) := by
    intro k q
    rw [der_fock hB c hc, inv_smul_smul₀ hc2]
  have key : fock c (KopL ε i j p) = (2 * c : ℂ)⁻¹ •
      ((∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) (fock c p))) -
        ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) (fock c p))) := by
    rw [kopL_apply, eL, map_sub, map_sum, map_sum, smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
  rw [key, op_id]
  by_cases hij : i = j
  · simp only [hij, if_true]
    module
  · simp only [hij, if_false, zero_smul, sub_zero, add_zero]
    module

end PositivityTheory.Rg.Sw.LC
end
end


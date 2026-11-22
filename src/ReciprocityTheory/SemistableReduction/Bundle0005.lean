import ReciprocityTheory.SemistableReduction.Bundle0003

-- bundled from ReciprocityTheory.SemistableReduction.ApproxBasisA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem approxB_jForm_add_right (p : ℕ) {r : ℕ} (x y z : Fin r → ℂ) :
    jForm p x (y + z) = jForm p x y + jForm p x z := by
  simp only [jForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem approxB_jForm_smul_right (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p x (a • y) = a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem approxB_jForm_sub_right (p : ℕ) {r : ℕ} (x y z : Fin r → ℂ) :
    jForm p x (y - z) = jForm p x y - jForm p x z := by
  simp only [jForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem approxB_jForm_sum_right (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (x : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p x (∑ j ∈ s, f j) = ∑ j ∈ s, jForm p x (f j) := by
  simp only [jForm, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem approxB_jForm_smul_left (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p (a • x) y = conj a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem approxB_jForm_sum_left (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (y : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  simp only [jForm, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem approxB_jForm_conj (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : conj (jForm p x y) = jForm p y x := by
  rw [jForm, jForm, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (k : ℕ) < p <;> simp [sgn, h, mul_comm]

theorem approxB_posSq_nonneg (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity

theorem approxB_negSq_nonneg (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity

theorem approxB_normSq_nonneg {r : ℕ} (u : Fin r → ℂ) : 0 ≤ normSq u := Finset.sum_nonneg fun k _ => by positivity

theorem approxB_posSq_add_negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    posSq p u + negSq p u = normSq u := by
  rw [posSq, negSq, normSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

theorem approxB_jForm_self (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    jForm p u u = ((posSq p u - negSq p u : ℝ) : ℂ) := by
  rw [jForm, posSq, negSq, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  by_cases h : (k : ℕ) < p <;> simp [sgn, h]

theorem approxB_jForm_self_re (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    (jForm p u u).re = posSq p u - negSq p u := by
  rw [approxB_jForm_self, Complex.ofReal_re]

theorem approxB_norm_jForm_self_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖jForm p u u‖ ≤ normSq u := by
  rw [approxB_jForm_self, Complex.norm_real, Real.norm_eq_abs, ← approxB_posSq_add_negSq]
  have h1 := approxB_posSq_nonneg p u
  have h2 := approxB_negSq_nonneg p u
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem approxB_normSq_add_le {r : ℕ} (a b : Fin r → ℂ) :
    normSq (a + b) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply]
  have h1 : ‖a k + b k‖ ^ 2 ≤ (‖a k‖ + ‖b k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]

theorem approxB_normSq_single {r : ℕ} (j : Fin r) (R : ℝ) :
    normSq ((R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) = R ^ 2 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp [sq_abs]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

abbrev ApproxPosIdx (r p : ℕ) := {j : Fin r // (j : ℕ) < p}

theorem approxB_sum_pos {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, ¬ (j : ℕ) < p → f j = 0) : ∑ j, f j = ∑ k : ApproxPosIdx r p, f k := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun j : Fin r => (j : ℕ) < p))
    (fun j _ hj => hf j (by simpa using hj))]
  exact Finset.sum_subtype _ (fun j => by simp) f

theorem approxB_sum_neg {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, (j : ℕ) < p → f j = 0) :
    ∑ j, f j = ∑ k : {j : Fin r // ¬ (j : ℕ) < p}, f k := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun j : Fin r => ¬ (j : ℕ) < p))
    (fun j _ hj => hf j (by simpa using hj))]
  exact Finset.sum_subtype _ (fun j => by simp) f

theorem approxB_card_pos {r p : ℕ} (hp : p ≤ r) : Fintype.card (ApproxPosIdx r p) = p := by
  let e : ApproxPosIdx r p ≃ Fin p :=
    { toFun := fun j => ⟨j.1, j.2⟩
      invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hp⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem approxB_card_neg {r p : ℕ} (hp : p ≤ r) :
    Fintype.card {j : Fin r // ¬ (j : ℕ) < p} = r - p := by
  rw [Fintype.card_subtype_compl, approxB_card_pos hp, Fintype.card_fin]

def approxPadPos {r p : ℕ} (x : ApproxPosIdx r p → ℂ) : Fin r → ℂ :=
  fun j => if h : (j : ℕ) < p then x ⟨j, h⟩ else 0

theorem approxB_pad_sum {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (X : Fin r → Fin r → ℂ) :
    ∑ j, approxPadPos x j • X j = ∑ k : ApproxPosIdx r p, x k • X k.1 := by
  rw [approxB_sum_pos (p := p) _ (fun j hj => by simp [approxPadPos, hj])]
  exact Finset.sum_congr rfl fun k _ => by simp [approxPadPos, k.2]

theorem approxB_pad_ne {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (hx : x ≠ 0) : approxPadPos x ≠ 0 := by
  intro h
  apply hx
  funext k
  have h1 := congr_fun h k.1
  simpa [approxPadPos, k.2] using h1

theorem approxB_pad_zero {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (j : Fin r) (hj : p ≤ (j : ℕ)) :
    approxPadPos x j = 0 := by
  simp [approxPadPos, not_lt.mpr hj]

theorem approxB_graph_pos {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)))
    (x : ApproxPosIdx r p → ℂ) :
    0 ≤ (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re ∧
    (x ≠ 0 → 0 < (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re) := by
  obtain ⟨h1, h2⟩ := hg (approxPadPos x) (fun j hj => approxB_pad_zero x j hj)
  rw [approxB_pad_sum] at h1 h2
  rw [approxB_jForm_self_re]
  have hρ' : (ρ / 3) ^ 2 ≤ 1 / 9 := by
    have h3 : ρ / 3 ≤ 1 / 3 := by linarith
    have h4 : 0 ≤ ρ / 3 := by linarith
    nlinarith
  have hp0 := approxB_posSq_nonneg p (∑ k, x k • X k.1)
  refine ⟨by nlinarith, fun hx => ?_⟩
  have h5 := h2 (approxB_pad_ne x hx)
  nlinarith

theorem approxB_gram_posSemidef {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) :
    (Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext k j
    simp [Matrix.conjTranspose_apply, approxB_jForm_conj]
  · have e : star x ⬝ᵥ ((Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)) *ᵥ x) =
        jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1) := by
      rw [approxB_jForm_sum_left]
      simp only [approxB_jForm_smul_left, approxB_jForm_sum_right, approxB_jForm_smul_right]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
        Complex.star_def]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, approxB_jForm_self]
    have h := (approxB_graph_pos hρ1 hρ X hg x).1
    rw [approxB_jForm_self_re] at h
    exact Complex.zero_le_real.mpr (by linarith)

theorem approxB_det_le_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (hN : N.PosSemidef)
    (c : ℝ) (hc : ∀ k, (N k k).re ≤ c) : ‖N.det‖ ≤ c ^ Fintype.card n := by
  classical
  have hH := hN.isHermitian
  have hdet : N.det = ∏ i, (hH.eigenvalues i : ℂ) := hH.det_eq_prod_eigenvalues
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hN.eigenvalues_nonneg
  have htr : ∑ i, hH.eigenvalues i = ∑ k, (N k k).re := by
    have h2 := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hnorm : ‖N.det‖ = ∏ i, hH.eigenvalues i := by
    rw [hdet, norm_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hl i)]
  rw [hnorm]
  have hsum : ∑ i, hH.eigenvalues i ≤ Fintype.card n * c := by
    rw [htr]
    calc ∑ k, (N k k).re ≤ ∑ _k : n, c := Finset.sum_le_sum fun k _ => hc k
      _ = Fintype.card n * c := by simp
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    simp [h0]
  · have hm : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    have hAM := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / Fintype.card n)
      hH.eigenvalues (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp) (fun i _ => hl i)
    have h2 : ∑ i, (1 : ℝ) / Fintype.card n * hH.eigenvalues i ≤ c := by
      rw [← Finset.mul_sum, div_mul_eq_mul_div, one_mul, div_le_iff₀ hm]
      linarith
    have hG : 0 ≤ ∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hl i) _
    calc ∏ i, hH.eigenvalues i = (∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n)) ^ Fintype.card n := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hl i), one_div_mul_cancel hm.ne', Real.rpow_one]
      _ ≤ c ^ Fintype.card n := pow_le_pow_left₀ hG (hAM.trans h2) _

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ApproxGraphA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

def posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then u k else 0

def negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then 0 else u k

def euc {r : ℕ} (u : Fin r → ℂ) : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 u

lemma euc_add {r : ℕ} (u v : Fin r → ℂ) : euc (u + v) = euc u + euc v := rfl

lemma euc_smul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) : euc (c • u) = c • euc u := rfl

lemma normSq_eq_euc {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq, euc]

lemma posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = ‖euc (posPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold posSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, posPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = ‖euc (negPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold negSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, negPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma normSq_split (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : normSq u = posSq p u + negSq p u := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma posPart_add_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p u + negPart p u = u := by
  funext k
  simp only [posPart, negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    posPart p (u + v) = posPart p u + posPart p v := by
  funext k
  simp only [posPart, Pi.add_apply]
  split_ifs <;> simp

lemma negPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    negPart p (u + v) = negPart p u + negPart p v := by
  funext k
  simp only [negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    posPart p (c • u) = c • posPart p u := by
  funext k
  simp only [posPart, Pi.smul_apply]
  split_ifs <;> simp

lemma negPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    negPart p (c • u) = c • negPart p u := by
  funext k
  simp only [negPart, Pi.smul_apply]
  split_ifs <;> simp

lemma inner_euc {r : ℕ} (x y : Fin r → ℂ) : inner ℂ (euc x) (euc y) = ∑ k, conj (x k) * y k := by
  simp [euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma jForm_eq (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) :
    jForm p x y = inner ℂ (euc (posPart p x)) (euc (posPart p y)) -
      inner ℂ (euc (negPart p x)) (euc (negPart p y)) := by
  rw [inner_euc, inner_euc, ← Finset.sum_sub_distrib]
  unfold jForm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn, posPart, negPart]
  split_ifs <;> simp

lemma jForm_self (p : ℕ) {r : ℕ} (y : Fin r → ℂ) :
    jForm p y y = ((posSq p y - negSq p y : ℝ) : ℂ) := by
  unfold jForm posSq negSq
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  unfold sgn
  split_ifs <;> simp

lemma norm_posPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (posPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := posSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (posPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma norm_negPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (negPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := negSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (negPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma euc_zero {r : ℕ} : euc (0 : Fin r → ℂ) = 0 := by
  rfl

lemma euc_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    euc (∑ j ∈ s, f j) = ∑ j ∈ s, euc (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact euc_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]

lemma euc_eq_zero {r : ℕ} {w : Fin r → ℂ} (h : euc w = 0) : w = 0 := by
  have h' := congrArg WithLp.ofLp h
  simpa [euc] using h'

lemma sum_norm_le_sqrt {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)
  rw [EuclideanSpace.norm_eq]
  simpa [euc] using h

lemma sum_smul_eq {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) (c : ℂ) :
    ∑ j, w j • X j = c • w + ∑ j, w j • (X j - c • (Pi.single j 1 : Fin r → ℂ)) := by
  funext k
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply]
  simp [Finset.mul_sum]
  ring

lemma norm_err_le {r p : ℕ} {μ R : ℝ} (X : Fin r → Fin r → ℂ)
    (hX : ∀ j : Fin r, (j : ℕ) < p → normSq (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (hμ : 0 ≤ μ) (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := by
  have he : ∀ j : Fin r, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ ≤ ‖w j‖ * μ := by
    intro j
    by_cases hj : (j : ℕ) < p
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := hX j hj
      rw [normSq_eq_euc] at h1
      have ha := norm_nonneg (euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))
      by_contra h
      push_neg at h
      nlinarith
    · rw [hw j (not_lt.mp hj)]
      simp
  calc ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖
      = ‖∑ j, w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        rw [euc_sum]
        simp only [euc_smul]
    _ ≤ ∑ j, ‖w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        simp only [norm_smul]
    _ ≤ ∑ j, ‖w j‖ * μ := Finset.sum_le_sum fun j _ => he j
    _ = μ * ∑ j, ‖w j‖ := by
        rw [Finset.mul_sum]
        simp only [mul_comm]
    _ ≤ μ * (√(r : ℝ) * ‖euc w‖) := mul_le_mul_of_nonneg_left (sum_norm_le_sqrt w) hμ
    _ = √(r : ℝ) * μ * ‖euc w‖ := by ring

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

-- bundled from ReciprocityTheory.SemistableReduction.BalancedSchwarz
section
namespace ReciprocityTheory.MultiplicativeHeights

open Metric Set

theorem bs_mem_of_gauge_lt_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (hs : IsOpen s) (hb : Balanced ℂ s) (h0 : (0 : E) ∈ s) {x : E} (hx : gauge s x < 1) :
    x ∈ s := by
  have habs : Absorbent ℝ s := absorbent_nhds_zero (hs.mem_nhds h0)
  obtain ⟨b, hb0, hb1, y, hy, rfl⟩ := exists_lt_of_gauge_lt habs hx
  have : (b : ℂ) • y ∈ s := hb.smul_mem (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; exact hb1.le) hy
  simpa [Complex.coe_smul] using this

theorem bs_key {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set E) (g : E → ℂ)
    (M : ℝ) (hs : IsOpen s) (hb : Balanced ℂ s) (hg : DifferentiableOn ℂ g s)
    (hM : ∀ w ∈ s, ‖g w‖ ≤ M) (h0 : (0 : E) ∈ s) (z : E) (R : ℝ) (hR : 1 < R)
    (hRt : R * gauge s z ≤ 1) : ‖g z - g 0‖ ≤ (M + ‖g 0‖) / R := by
  have hmaps : MapsTo (fun ζ : ℂ => ζ • z) (ball (0 : ℂ) R) s := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ
    apply bs_mem_of_gauge_lt_one hs hb h0
    rw [gauge_smul hb]
    calc ‖ζ‖ * gauge s z ≤ ‖ζ‖ * (1 / R) := by
          gcongr
          rw [le_div_iff₀ (by linarith)]; linarith
      _ < R * (1 / R) := by
          gcongr
      _ = 1 := by field_simp
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => g (ζ • z)) (ball (0 : ℂ) R) :=
    hg.comp (differentiableOn_id.smul_const z) hmaps
  have hm2 : MapsTo (fun ζ : ℂ => g (ζ • z)) (ball (0 : ℂ) R)
      (closedBall ((fun ζ : ℂ => g (ζ • z)) 0) (M + ‖g 0‖)) := by
    intro ζ hζ
    simp only [zero_smul, mem_closedBall, dist_eq_norm]
    calc ‖g (ζ • z) - g 0‖ ≤ ‖g (ζ • z)‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ M + ‖g 0‖ := by gcongr; exact hM _ (hmaps hζ)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_one]; exact hR
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm2 h1
  simpa [dist_eq_norm] using this

theorem balancedSchwarz_holds : BalancedSchwarzStatement := by
  intro E _ _ s g M hs hb hg hM z hz
  have h0 : (0 : E) ∈ s := by simpa using hb.smul_mem (a := (0 : ℂ)) (by simp) hz
  have ht0 : 0 ≤ gauge s z := gauge_nonneg z
  have ht1 : gauge s z < 1 := gauge_lt_one_of_mem_of_isOpen hs hz
  have hN : 0 ≤ M + ‖g 0‖ := by
    have := hM 0 h0; have := norm_nonneg (g 0); linarith
  rcases ht0.lt_or_eq with hpos | hzero
  · have := bs_key s g M hs hb hg hM h0 z (1 / gauge s z)
      (by rw [lt_div_iff₀ hpos]; linarith) (by field_simp; rfl)
    simpa [div_eq_mul_inv, mul_comm] using this
  · rw [← hzero, mul_zero]
    by_contra hne'
    have hne := not_le.mp hne'
    set d := ‖g z - g 0‖
    have hR : 1 < (M + ‖g 0‖) / d * 2 + 2 := by
      have : 0 ≤ (M + ‖g 0‖) / d * 2 := by positivity
      linarith
    have := bs_key s g M hs hb hg hM h0 z ((M + ‖g 0‖) / d * 2 + 2) hR
      (by rw [← hzero, mul_zero]; exact zero_le_one)
    rw [le_div_iff₀ (by linarith)] at this
    have h3 : d * ((M + ‖g 0‖) / d * 2 + 2) = 2 * (M + ‖g 0‖) + 2 * d := by
      field_simp
    nlinarith

end ReciprocityTheory.MultiplicativeHeights
end


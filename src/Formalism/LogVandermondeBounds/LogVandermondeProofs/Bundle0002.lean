import Formalism.LogVandermondeBounds.Bundle0001

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Core

variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]

def eps (a h : H) : K := if h = a then 1 else if h = 1 then -1 else 0

def bas (a : ι → {c : H // c ≠ 1}) (h : ι → H) : K := ∏ w, (eps ((a w : H)) (h w) : K)

omit [Fintype H] in
lemma mulSingle_mul_apply_ne (v w : ι) (c : H) (h : ι → H) (hw : w ≠ v) :
    ((Pi.mulSingle v c : ι → H) * h) w = h w := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, _root_.one_mul]

omit [Fintype H] in
lemma mulSingle_mul_apply_self (v : ι) (c : H) (h : ι → H) :
    ((Pi.mulSingle v c : ι → H) * h) v = c * h v := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same]

lemma sum_eps (a t : H) (ha : a ≠ 1) : ∑ c : H, (eps a (c * t) : K) = 0 := by
  have key : ∀ h : H, (eps a h : K) = (if h = a then 1 else 0) + (if h = 1 then -1 else 0) := by
    intro h
    unfold eps
    by_cases h1 : h = a
    · subst h1
      simp [ha]
    · simp [h1]
  rw [show (∑ c : H, (eps a (c * t) : K)) = ∑ h : H, (eps a h : K) from
    Equiv.sum_comp (Equiv.mulRight t) (fun h => (eps a h : K))]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma sum_bas (a : ι → {c : H // c ≠ 1}) (v : ι) (h : ι → H) :
    ∑ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K) = 0 := by
  have hfac : ∀ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K)
      = (eps (a v : H) (c * h v) : K) * ∏ w ∈ univ.erase v, (eps (a w : H) (h w) : K) := by
    intro c
    unfold bas
    rw [← Finset.mul_prod_erase univ _ (mem_univ v)]
    simp only [mulSingle_mul_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mulSingle_mul_apply_ne v w c h (Finset.ne_of_mem_erase hw)]
  simp only [hfac, ← Finset.sum_mul, sum_eps (K := K) (a v : H) (h v) (a v).2, zero_mul]

lemma bas_avoid (a b : ι → {c : H // c ≠ 1}) :
    (bas a (fun w => (b w : H)) : K) = if a = b then 1 else 0 := by
  unfold bas
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold eps
    simp
  · rw [if_neg hab]
    have hw : ∃ w, a w ≠ b w := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hab (funext hcon)
    obtain ⟨w, hw⟩ := hw
    refine Finset.prod_eq_zero (mem_univ w) ?_
    have h1 : (b w : H) ≠ a w := fun h => hw (Subtype.ext h.symm)
    unfold eps
    simp [h1, (b w).2]

lemma inj_core (ψ : (ι → H) → K)
    (hψ : ∀ (v : ι) (h : ι → H), ∑ c : H, ψ ((Pi.mulSingle v c : ι → H) * h) = 0)
    (h0 : ∀ a : ι → {c : H // c ≠ 1}, ψ (fun w => (a w : H)) = 0) :
    ∀ h, ψ h = 0 := by
  classical
  suffices key : ∀ n, ∀ h : ι → H, (univ.filter (fun w => h w = 1)).card = n → ψ h = 0 from
    fun h => key _ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn
    by_cases hall : ∀ w, h w ≠ 1
    · exact h0 (fun w => ⟨h w, hall w⟩)
    · simp only [not_forall, not_not] at hall
      obtain ⟨v, hv⟩ := hall
      have hsum := hψ v h
      rw [Finset.sum_eq_single (1 : H)] at hsum
      · simpa using hsum
      · intro c _ hc
        apply ih _ _ _ rfl
        rw [← hn]
        have hset : univ.filter (fun w => ((Pi.mulSingle v c : ι → H) * h) w = 1)
            = (univ.filter (fun w => h w = 1)).erase v := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hwv : w = v
          · subst hwv
            rw [mulSingle_mul_apply_self, hv, mul_one]
            simp [hc]
          · rw [mulSingle_mul_apply_ne v w c h hwv]
            simp [hwv]
        rw [hset]
        exact Finset.card_erase_lt_of_mem (by simp [hv])
      · intro h1
        exact absurd (Finset.mem_univ _) h1

end Core

section Main

variable {ι H X K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H]
  [Fintype X] [MulAction (ι → H) X] [Field K]

def restr (Q : Type) (e : Q × (ι → H) ≃ X) :
    ramSub ι H X K →ₗ[K] (Q × (ι → {c : H // c ≠ 1}) → K) where
  toFun φ p := (φ : X → K) (e (p.1, fun w => (p.2 w : H)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_core (Q : Type) [Fintype Q] (e : Q × (ι → H) ≃ X)
    (he : ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g)) :
    Module.finrank K (ramSub ι H X K) = Fintype.card Q * (Fintype.card H - 1) ^ Fintype.card ι := by
  classical
  have hmem : ∀ φ : ramSub ι H X K, ∀ v x,
      ∑ c : H, (φ : X → K) ((Pi.mulSingle v c : ι → H) • x) = 0 := fun φ => φ.2
  have hinj : Function.Injective (restr (K := K) Q e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext x
    obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
    have hz := inj_core (K := K) (fun h => (φ : X → K) (e (ω, h)))
      (fun v h => by simpa only [he] using hmem φ v (e (ω, h)))
      (fun a => congrFun hφ (ω, a)) g
    simpa using hz
  have hsurj : Function.Surjective (restr (K := K) Q e) := by
    intro f
    let φ0 : X → K := fun x =>
      ∑ a : ι → {c : H // c ≠ 1}, f ((e.symm x).1, a) * bas a (e.symm x).2
    have hφ0 : φ0 ∈ ramSub ι H X K := by
      show ∀ (v : ι) (x : X), ∑ c : H, φ0 ((Pi.mulSingle v c : ι → H) • x) = 0
      intro v x
      obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
      have hx : ∀ c : H, e.symm ((Pi.mulSingle v c : ι → H) • e (ω, g))
          = (ω, (Pi.mulSingle v c : ι → H) * g) := by
        intro c
        rw [← he, Equiv.symm_apply_apply]
      simp only [φ0, hx]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.mul_sum, sum_bas, mul_zero]
    refine ⟨⟨φ0, hφ0⟩, ?_⟩
    funext p
    obtain ⟨ω, a'⟩ := p
    show φ0 (e (ω, fun w => (a' w : H))) = f (ω, a')
    simp only [φ0, Equiv.symm_apply_apply, bas_avoid]
    simp
  have hc : Fintype.card {c : H // c ≠ 1} = Fintype.card H - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [(LinearEquiv.ofBijective (restr (K := K) Q e) ⟨hinj, hsurj⟩).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fun, hc]

end Main

theorem exists_equiv (ι H X : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] (hfree : ∀ (g : ι → H) (x : X), g • x = x → g = 1) :
    ∃ (Q : Type) (_ : Fintype Q) (e : Q × (ι → H) ≃ X),
      ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g) := by
  classical
  let Q := MulAction.orbitRel.Quotient (ι → H) X
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → X := fun ω => Quotient.out ω
  have hrep : ∀ ω : Q, Quotient.mk (MulAction.orbitRel (ι → H) X) (rep ω) = ω :=
    fun ω => Quotient.out_eq ω
  let f : Q × (ι → H) → X := fun p => p.2 • rep p.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ω, g⟩ ⟨ω', g'⟩ h
      change g • rep ω = g' • rep ω' at h
      have hω : ω = ω' := by
        rw [← hrep ω, ← hrep ω']
        apply Quotient.sound
        show rep ω ∈ MulAction.orbit (ι → H) (rep ω')
        refine ⟨g⁻¹ * g', ?_⟩
        show (g⁻¹ * g') • rep ω' = rep ω
        rw [mul_smul, ← h, inv_smul_smul]
      subst hω
      have hfix : (g'⁻¹ * g) • rep ω = rep ω := by rw [mul_smul, h, inv_smul_smul]
      have hg := hfree _ _ hfix
      rw [inv_mul_eq_one] at hg
      rw [hg]
    · intro x
      have hx : rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) ∈ MulAction.orbit (ι → H) x :=
        Quotient.exact (hrep _)
      obtain ⟨g, hg⟩ := hx
      refine ⟨(Quotient.mk (MulAction.orbitRel (ι → H) X) x, g⁻¹), ?_⟩
      show g⁻¹ • rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) = x
      rw [← hg, inv_smul_smul]
  refine ⟨Q, inferInstance, Equiv.ofBijective f hf, ?_⟩
  intro m ω g
  show (m * g) • rep ω = m • (g • rep ω)
  rw [mul_smul]

theorem finrankFiberSumZero : FinrankFiberSumZero := by
  intro ι H X K _ _ _ _ _ _ _ hfree
  classical
  obtain ⟨Q, _, e, he⟩ := exists_equiv ι H X hfree
  rw [finrank_core (K := K) Q e he, ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  ring

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric
section
namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

lemma key_ineq (x : ℚ) (hx : 2 ≤ x) :
    ∀ i j : ℕ, i ≤ j → (i, j) ≠ (0, 0) →
      x ^ 3 - 2 * x ^ 2 + 3 ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) := by
  have hq : 1 ≤ x ^ 2 := by nlinarith

  have step : ∀ i j : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + 1) - (x ^ 2 - 1) * ((i : ℚ) + (j + 1 : ℕ) + 1) := by
    intro i j
    have hA : 1 ≤ (x ^ 2) ^ j := one_le_pow₀ hq
    have hB : 1 ≤ x * (x ^ 2) ^ j := by nlinarith
    push_cast
    rw [pow_succ (x ^ 2) j]
    have hq0 : 0 ≤ x ^ 2 - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hB hq0]
  have mono : ∀ i j k : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + k) - (x ^ 2 - 1) * ((i : ℚ) + (j + k : ℕ) + 1) := by
    intro i j k
    induction k with
    | zero => simp
    | succ k ih => exact ih.trans (by simpa [Nat.add_assoc] using step i (j + k))

  have diag : ∀ m : ℕ, x ^ 3 - 2 * x ^ 2 + 3 ≤
      (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) - (x ^ 2 - 1) * (((m + 1 : ℕ) : ℚ) + (m + 1 : ℕ) + 1) := by
    intro m
    induction m with
    | zero => push_cast; ring_nf; linarith
    | succ m ih =>
      have hA : 1 ≤ (x ^ 2) ^ (m + 1) := one_le_pow₀ hq
      have hB : 2 ≤ (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) := by nlinarith
      refine ih.trans ?_
      push_cast at *
      rw [pow_succ (x ^ 2) (m + 1)]
      nlinarith
  intro i j hij hne
  rcases Nat.eq_zero_or_pos i with rfl | hi
  ·
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd rfl hne
      · exact hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    refine le_trans ?_ (mono 0 1 k)
    push_cast; ring_nf; linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := mono (1 + m) (1 + m) k
    have h2 := diag m
    rw [Nat.add_comm 1 m] at *
    linarith

lemma sq_ge_two (p : ℕ) (hp : 2 ≤ p) : 2 ≤ p ^ 2 := by nlinarith

lemma coefL_pow (p j : ℕ) (hp : 2 ≤ p) : coefL p ((p ^ 2) ^ j) = 1 / (p : ℚ) ^ j := by
  have h : ∃ j', (p ^ 2) ^ j = (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefL
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) (Classical.choose_spec h)
  rw [← hj]

lemma coefL_zero (p a : ℕ) (h : ¬∃ j, a = (p ^ 2) ^ j) : coefL p a = 0 := by
  unfold coefL
  rw [dif_neg h]

lemma coefG_pow (p j : ℕ) (hp : 2 ≤ p) : coefG p (p * (p ^ 2) ^ j) = 1 / (p : ℚ) ^ (j + 1) := by
  have h : ∃ j', p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefG
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp)
    (Nat.eq_of_mul_eq_mul_left (by omega) (Classical.choose_spec h))
  rw [← hj]

lemma coefG_zero (p a : ℕ) (h : ¬∃ j, a = p * (p ^ 2) ^ j) : coefG p a = 0 := by
  unfold coefG
  rw [dif_neg h]

lemma coefA_pow (p i j : ℕ) (hp : 2 ≤ p) :
    coefA p ((p ^ 2) ^ i) (p * (p ^ 2) ^ j) = if i ≤ j then 1 / (p : ℚ) ^ (i + j + 1) else 0 := by
  unfold coefA
  by_cases hij : i ≤ j
  · have h : ∃ i' j', i' ≤ j' ∧ (p ^ 2) ^ i = (p ^ 2) ^ i' ∧ p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' :=
      ⟨i, j, hij, rfl, rfl⟩
    rw [dif_pos h, if_pos hij]
    obtain ⟨-, h2, h3⟩ := Classical.choose_spec (Classical.choose_spec h)
    have hi : i = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = Classical.choose (Classical.choose_spec h) :=
      Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    rw [← hj, ← hi]
  · rw [if_neg hij, dif_neg]
    rintro ⟨i', j', h1, h2, h3⟩
    have hi : i = i' := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = j' := Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    subst hi hj
    exact hij h1

lemma coefA_zero (p a b : ℕ) (h : ¬∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j) :
    coefA p a b = 0 := by
  unfold coefA
  rw [dif_neg h]

theorem logarithm_series_coefficient_identities : LogarithmSeriesIdentities := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  constructor
  · intro a
    by_cases hd : p ∣ a
    · obtain ⟨c, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p c), Nat.mul_div_cancel_left c hp0]
      have ha1 : p * c ≠ 1 := by
        intro h
        rcases c with _ | c
        · simp at h
        · nlinarith
      rw [if_neg ha1, sub_zero]
      by_cases hc : ∃ k, c = p * (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hc
        rw [coefG_pow p k hp2, show p * (p * (p ^ 2) ^ k) = (p ^ 2) ^ (k + 1) by ring, coefL_pow p _ hp2]
      · rw [coefG_zero p c hc, coefL_zero]
        rintro ⟨j, hj⟩
        rcases j with _ | k
        · rw [pow_zero] at hj
          exact ha1 hj
        · apply hc
          refine ⟨k, ?_⟩
          have : p * c = p * (p * (p ^ 2) ^ k) := by rw [hj]; ring
          exact Nat.eq_of_mul_eq_mul_left hp0 this
    · rw [if_neg hd]
      by_cases ha : a = 1
      · subst ha
        have h1 := coefL_pow p 0 hp2
        rw [pow_zero, pow_zero] at h1
        rw [if_pos rfl, h1]
        norm_num
      · rw [if_neg ha, sub_zero, coefL_zero]
        rintro ⟨j, rfl⟩
        rcases j with _ | k
        · exact ha (pow_zero _)
        · exact hd (dvd_pow (dvd_pow_self p two_ne_zero) (Nat.succ_ne_zero k))
  · intro a b
    by_cases hA : ∃ i, a = p * (p ^ 2) ^ i
    · obtain ⟨i, rfl⟩ := hA
      rw [coefG_pow p i hp2]
      by_cases hB : ∃ k, b = (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hB
        simp only [coefB]
        rw [coefL_pow p k hp2, coefA_pow p k i hp2]
        rcases k with _ | j
        · have hn : ¬(p ∣ p * (p ^ 2) ^ i ∧ p ∣ (p ^ 2) ^ 0) := by
            rintro ⟨-, h⟩
            rw [pow_zero, Nat.dvd_one] at h
            omega
          rw [if_neg hn, if_pos (Nat.zero_le _)]
          field_simp
          ring
        · have hb : (p ^ 2) ^ (j + 1) = p * (p * (p ^ 2) ^ j) := by ring
          rw [hb, if_pos ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hp0,
            Nat.mul_div_cancel_left _ hp0, coefA_pow p i j hp2]
          by_cases h : i ≤ j
          · rw [if_pos h, if_neg (by omega)]
            field_simp
            ring
          · rw [if_neg h, if_pos (by omega)]
            field_simp
            ring
      · simp only [coefB]
        rw [coefL_zero p b hB, coefA_zero p b _ (by rintro ⟨i', j', -, h2, -⟩; exact hB ⟨i', h2⟩)]
        simp only [mul_zero, sub_zero]
        split_ifs with h
        · obtain ⟨-, c, rfl⟩ := h
          rw [Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0]
          apply coefA_zero
          rintro ⟨i', j', -, -, h3⟩
          exact hB ⟨j' + 1, by rw [h3]; ring⟩
        · rfl
    · simp only [coefB]
      rw [coefG_zero p a hA, coefA_zero p b a (by rintro ⟨i', j', -, -, h3⟩; exact hA ⟨j', h3⟩)]
      simp only [zero_mul, zero_sub, mul_zero, neg_zero]
      split_ifs with h
      · obtain ⟨⟨c, rfl⟩, -⟩ := h
        rw [Nat.mul_div_cancel_left _ hp0]
        apply coefA_zero
        rintro ⟨i', j', -, h2, -⟩
        exact hA ⟨i', by rw [h2]⟩
      · rfl

end Formalism.LogVandermondeBounds.TaylorLogMetric
end


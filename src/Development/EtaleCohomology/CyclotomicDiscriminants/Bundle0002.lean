import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SSteinTPf
section
noncomputable section

open NumberField IsDedekindDomain FractionalIdeal Matrix
open scoped nonZeroDivisors

namespace LateralTheory.Q.SSteinT

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem val_eq_count (P : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    P.valuation K x = WithZero.exp (-count K P (spanSingleton R⁰ x)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hx
  have h : spanSingleton R⁰ (algebraMap R K r / algebraMap R K s) =
      spanSingleton R⁰ (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_inv_mul]
  rw [count_well_defined K P (spanSingleton_ne_zero_iff.mpr hx) h, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg P hr0, HeightOneSpectrum.intValuation_if_neg P hs0,
    ← WithZero.exp_sub]
  congr 1
  ring

theorem val_le_of_mem (P : HeightOneSpectrum R) {I : FractionalIdeal R⁰ K} {x : K} (hx : x ∈ I) :
    P.valuation K x ≤ WithZero.exp (-count K P I) := by
  by_cases h0 : x = 0
  · simp [h0]
  rw [val_eq_count P x h0, WithZero.exp_le_exp, neg_le_neg_iff]
  exact count_mono K P (spanSingleton_ne_zero_iff.mpr h0) (spanSingleton_le_iff_mem.mpr hx)

theorem exists_frac (d : HeightOneSpectrum R →₀ ℤ) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ ∀ P, count K P I = d P := by
  refine ⟨d.prod fun P n => (P.asIdeal : FractionalIdeal R⁰ K) ^ n, ?_, fun P => count_finsuppProd K P d⟩
  refine Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ ?_
  exact coeIdeal_ne_zero.mpr P.ne_bot

theorem exists_sl2_with_valuation_bounds (d e : HeightOneSpectrum R →₀ ℤ) :
    ∃ p q r s : K, p ≠ 0 ∧ p * s - q * r = 1 ∧ ∀ P : HeightOneSpectrum R,
      P.valuation K p ≤ WithZero.exp (-d P) ∧ P.valuation K q ≤ WithZero.exp (-e P) ∧
      P.valuation K r ≤ WithZero.exp (-(-e P)) ∧ P.valuation K s ≤ WithZero.exp (-(-d P)) := by
  obtain ⟨C, hC, hCd⟩ := exists_frac (K := K) d
  obtain ⟨D, hD, hDe⟩ := exists_frac (K := K) e
  obtain ⟨p, hp0, hp⟩ := exists_ne_zero_mem_isInteger hC
  set p' := algebraMap R K p with hp'
  have hp'0 : p' ≠ 0 := by
    rw [hp']
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp0
  have h1 : spanSingleton R⁰ p' * C⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hC]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.mpr hp) _
  obtain ⟨q, hq⟩ := exists_add_spanSingleton_mul_eq h1
    (mul_ne_zero (spanSingleton_ne_zero_iff.mpr hp'0) (inv_ne_zero hC)) (inv_ne_zero hD)
  have hqD : q ∈ D := by
    have h2 : spanSingleton R⁰ q * D⁻¹ ≤ 1 := by
      rw [← hq]
      exact le_sup_right
    have h3 : spanSingleton R⁰ q * D⁻¹ * D ≤ 1 * D := mul_le_mul_left h2 _
    rw [inv_mul_cancel_right₀ hD, one_mul] at h3
    exact spanSingleton_le_iff_mem.mp h3
  have h4 : (1 : K) ∈ spanSingleton R⁰ p' * C⁻¹ + spanSingleton R⁰ q * D⁻¹ := by
    rw [hq]
    exact one_mem_one _
  obtain ⟨u, hu, w, hw, huw⟩ := (mem_add _ _ _).mp h4
  obtain ⟨s, hs, rfl⟩ := mem_singleton_mul.mp hu
  obtain ⟨r, hr, rfl⟩ := mem_singleton_mul.mp hw
  refine ⟨p', q, -r, s, hp'0, by rw [← huw]; ring, fun P => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← hCd]; exact val_le_of_mem P hp
  · rw [← hDe]; exact val_le_of_mem P hqD
  · rw [← hDe, ← count_inv, Valuation.map_neg]; exact val_le_of_mem P hr
  · rw [← hCd, ← count_inv]; exact val_le_of_mem P hs

theorem val_comb (P : HeightOneSpectrum R) {u x u' x' : K} {m a m' a' c : ℤ}
    (hu : P.valuation K u ≤ WithZero.exp (-m)) (hx : P.valuation K x ≤ WithZero.exp (-a))
    (hu' : P.valuation K u' ≤ WithZero.exp (-m')) (hx' : P.valuation K x' ≤ WithZero.exp (-a'))
    (h : c = m + a) (h' : c = m' + a') : P.valuation K (u * x + u' * x') ≤ WithZero.exp (-c) := by
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, h, neg_add, WithZero.exp_add]; exact mul_le_mul' hu hx
  · rw [map_mul, h', neg_add, WithZero.exp_add]; exact mul_le_mul' hu' hx'

variable {J : Type} [Fintype J] [DecidableEq J]

def Lat (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (x : J → K) : Prop :=
  ∀ j P, P.valuation K (x j) ≤ WithZero.exp (-𝔞 j P)

def Rel (𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ) (β : K) : Prop :=
  ∃ M : Matrix J J K, M.det = β ∧ ∀ x : J → K, Lat 𝔞 x ↔ Lat 𝔟 (M *ᵥ x)

theorem Rel.refl (𝔞 : J → HeightOneSpectrum R →₀ ℤ) : Rel 𝔞 𝔞 (1 : K) :=
  ⟨1, det_one, fun x => by rw [one_mulVec]⟩

theorem Rel.trans {𝔞 𝔟 𝔠 : J → HeightOneSpectrum R →₀ ℤ} {β γ : K} (h : Rel 𝔞 𝔟 β) (h' : Rel 𝔟 𝔠 γ) :
    Rel 𝔞 𝔠 (γ * β) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨N, hN, h'⟩ := h'
  exact ⟨N * M, by rw [det_mul, hM, hN], fun x => by rw [h, h', mulVec_mulVec]⟩

theorem exists_block {i j : J} (hij : i ≠ j) {p q r s : K} (hp : p ≠ 0) (h : p * s - q * r = 1) :
    ∃ M : Matrix J J K, M.det = 1 ∧ ∀ x : J → K, (M *ᵥ x) i = p * x i + q * x j ∧
      (M *ᵥ x) j = r * x i + s * x j ∧ ∀ k, k ≠ i → k ≠ j → (M *ᵥ x) k = x k := by
  refine ⟨transvection j i (r / p) * diagonal (Pi.mulSingle i p * Pi.mulSingle j p⁻¹) *
    transvection i j (q / p), ?_, fun x => ?_⟩
  · rw [det_mul, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, det_diagonal]
    simp [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', hp]
  · have hs : s = (1 + q * r) / p := by
      rw [← h]; field_simp; ring
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine ⟨?_, ?_, fun k hk hk' => ?_⟩
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm]
      field_simp
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm, hs]
      field_simp
      ring
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hk, hk']

theorem rel_move {i j : J} (hij : i ≠ j) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) :
    Rel 𝔞 (𝔞 + Pi.single i d - Pi.single j d) (1 : K) := by
  obtain ⟨p, q, r, s, hp, h, hv⟩ := exists_sl2_with_valuation_bounds (K := K) d (𝔞 i + d - 𝔞 j)
  obtain ⟨M, hM, hx⟩ := exists_block hij hp h
  refine ⟨M, hM, fun x => ?_⟩
  obtain ⟨hi, hj, hk⟩ := hx x
  constructor
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      rw [hi]
      refine val_comb P h1 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij] <;> ring
    by_cases hkj : k = j
    · subst hkj
      rw [hj]
      refine val_comb P h3 (H i P) h4 (H k P) ?_ ?_ <;> simp [hij.symm] <;> ring
    · rw [hk k hki hkj]
      simpa [hki, hkj] using H k P
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      have : x k = s * (M *ᵥ x) k + (-q) * (M *ᵥ x) j := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h2
      refine val_comb P h4 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    by_cases hkj : k = j
    · subst hkj
      have : x k = (-r) * (M *ᵥ x) i + p * (M *ᵥ x) k := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h3
      refine val_comb P h3 (H i P) h1 (H k P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    · have := H k P
      rw [hk k hki hkj] at this
      simpa [hki, hkj] using this

theorem rel_of_sum_eq (j₀ : J) (S : Finset J) : ∀ 𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ,
    (∀ j, j ∉ S → j ≠ j₀ → 𝔞 j = 𝔟 j) → ∑ j, 𝔞 j = ∑ j, 𝔟 j → Rel 𝔞 𝔟 (1 : K) := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝔞 𝔟 h hs
    have : 𝔞 = 𝔟 := by
      funext j
      by_cases hj : j = j₀
      · subst hj
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ 𝔟 (Finset.mem_univ j),
          Finset.sum_congr rfl fun k hk => h k (by simp) (Finset.ne_of_mem_erase hk)] at hs
        exact add_right_cancel hs
      · exact h j (by simp) hj
    rw [this]
    exact Rel.refl 𝔟
  | insert i S hi ih =>
    intro 𝔞 𝔟 h hs
    by_cases hi₀ : i = j₀
    · exact ih 𝔞 𝔟 (fun j hj hj' => h j (by simp [hj, hi₀, hj']) hj') hs
    have h1 := rel_move (K := K) hi₀ 𝔞 (𝔟 i - 𝔞 i)
    have h2 := ih (𝔞 + Pi.single i (𝔟 i - 𝔞 i) - Pi.single j₀ (𝔟 i - 𝔞 i)) 𝔟 (fun j hj hj' => by
      by_cases hji : j = i
      · subst hji; simp [hj']
      · simpa [hji, hj'] using h j (by simp [hj, hji]) hj') (by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs])
    simpa using h1.trans h2

theorem rel_scale (j₀ : J) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) (β : K)
    (hβ : ∀ P : HeightOneSpectrum R, P.valuation K β = WithZero.exp (-d P)) :
    Rel 𝔞 (𝔞 + Pi.single j₀ d) β := by
  refine ⟨diagonal (Pi.mulSingle j₀ β), by simp [det_diagonal, Finset.prod_pi_mulSingle'], fun x => ?_⟩
  refine forall_congr' fun j => forall_congr' fun P => ?_
  by_cases hj : j = j₀
  · subst hj
    rw [mulVec_diagonal, Pi.mulSingle_eq_same, map_mul, hβ, Pi.add_apply, Pi.single_eq_same, Finsupp.add_apply,
      neg_add, WithZero.exp_add, mul_comm, mul_le_mul_iff_left₀ WithZero.exp_pos]
  · simp [mulVec_diagonal, hj]

open UpperTheory.V.ZK in
theorem SStein_of : UpperTheory.V.ZK.SStein := by
  intro F _ _ J _ 𝔞 𝔟 β hJ hβ
  classical
  have key : Rel (R := 𝓞 F) (K := F) 𝔞 𝔟 (β : F) := by
    rcases isEmpty_or_nonempty J with hE | ⟨⟨j₀⟩⟩
    · have h1 : β = 1 := hJ.resolve_left (not_nonempty_iff.mpr hE)
      rw [h1, Units.val_one, Subsingleton.elim 𝔞 𝔟]
      exact @Rel.refl _ _ _ _ _ _ _ _ _ (_) 𝔟
    · have h1 := rel_scale (K := F) j₀ 𝔞 (∑ j, (𝔟 j - 𝔞 j)) β fun P => by
        have h0 : P.valuation F (β : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr β.ne_zero
        have h2 : (∑ j, (𝔟 j - 𝔞 j)) P = ordP P β := by
          rw [hβ, Finsupp.finsetSum_apply]; rfl
        rw [h2, ordP, neg_neg, WithZero.exp_log h0]
      have h2 := rel_of_sum_eq (K := F) j₀ Finset.univ (𝔞 + Pi.single j₀ (∑ j, (𝔟 j - 𝔞 j))) 𝔟 (by simp)
        (by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib])
      simpa using h1.trans h2
  obtain ⟨M, hM, h⟩ := key
  have hU : IsUnit M.det := hM ▸ β.isUnit
  refine ⟨Matrix.toLinearEquiv (Pi.basisFun F J) M hU, ?_, fun x => ?_⟩
  · ext
    rw [LinearEquiv.coe_det, ← hM, ← LinearMap.det_toLin (Pi.basisFun F J) M]
    congr 1
  · have : Matrix.toLinearEquiv (Pi.basisFun F J) M hU x = M *ᵥ x := by
      rw [Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    rw [this]
    exact h x

end LateralTheory.Q.SSteinT
end
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SZcTPf
section
noncomputable section

namespace LateralTheory.Q.SZcT

open UpperTheory.V.ZK

def wd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

theorem zc_eq (q : ℕ) [NeZero q] (e : ℕ) :
    zc q e = ∑ j : Fin (e + 1) → ZMod q, Finsupp.single (wd e j) 1 := rfl

theorem alt_range {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (T : ℕ → M) (n : ℕ)
    (h : ∀ a, a < n → T (2 * a) = T (2 * a + 1)) :
    ∑ p ∈ Finset.range (2 * n), ((-1 : A) ^ (p + 1)) • T p = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih fun a ha => h a (by omega), ← h n (by omega), pow_succ (-1 : A) (2 * n + 1)]
    simp

theorem alt_fin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (e : ℕ) (S : Fin (2 * e + 1 + 1) → M)
    (h : ∀ (a : ℕ) (ha : a < e + 1), S ⟨2 * a, by omega⟩ = S ⟨2 * a + 1, by omega⟩) :
    ∑ p : Fin (2 * e + 1 + 1), ((-1 : A) ^ ((p : ℕ) + 1)) • S p = 0 := by
  have key := alt_range (A := A) (fun p => if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0) (e + 1) (by
    intro a ha
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact h a ha)
  rw [show 2 * (e + 1) = 2 * e + 1 + 1 by ring, ← Fin.sum_univ_eq_sum_range
    (fun p => ((-1 : A) ^ (p + 1)) • (if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0))] at key
  rw [← key]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [dif_pos p.2]

theorem wd_even {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1)) (k : Fin (e + 1))
    (h : (i : ℕ) = 2 * k) : wd e j i = Multiplicative.ofAdd (j k) := by
  unfold wd
  rw [if_pos (by omega)]
  congr 2
  ext
  show (i : ℕ) / 2 = k
  omega

theorem wd_odd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : (i : ℕ) % 2 = 1) : wd e j i = Multiplicative.ofAdd 1 := by
  unfold wd
  rw [if_neg (by omega)]

theorem wd_congr {q : ℕ} (e : ℕ) (j j' : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : ∀ k : Fin (e + 1), (i : ℕ) = 2 * k → j k = j' k) : wd e j i = wd e j' i := by
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have hk : (i : ℕ) = 2 * ((⟨i / 2, by omega⟩ : Fin (e + 1)) : ℕ) := by
      show (i : ℕ) = 2 * (i / 2)
      omega
    rw [wd_even e j i _ hk, wd_even e j' i _ hk, h _ hk]
  · rw [wd_odd e j i hi, wd_odd e j' i hi]

theorem tail_sum (q : ℕ) [NeZero q] (e : ℕ) :
    (∑ j : Fin (e + 1) → ZMod q, Finsupp.single (fun i : Fin (2 * e + 1) => wd e j i.succ) 1 :
      Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h : ∀ x : ZMod q, (fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (x, j)) i.succ) =
      fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (0, j)) i.succ := by
    intro x
    funext i
    refine wd_congr e _ _ _ fun k hk => ?_
    induction k using Fin.cases with
    | zero => simp at hk
    | succ k => simp [Fin.consEquiv]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, Finsupp.smul_single]
  simp

def sh (q e a : ℕ) : Fin (e + 1) → ZMod q := fun k => if (k : ℕ) = a then 1 else if (k : ℕ) = a + 1 then -1 else 0

theorem contract_eq {q : ℕ} (e a : ℕ) (ha : a < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * a, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e j) =
      Fin.contractNth (⟨2 * a + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e (j + sh q e a)) := by
  funext i
  have hi := i.2
  rcases lt_trichotomy (i : ℕ) (2 * a) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega)]
    refine wd_congr e _ _ _ fun k hk => ?_
    rw [Fin.val_castSucc] at hk
    rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega),
      wd_even e j i.castSucc ⟨a, ha⟩ h, wd_even e _ i.castSucc ⟨a, ha⟩ h,
      wd_odd e j i.succ (by rw [Fin.val_succ]; omega), Pi.add_apply, sh, if_pos rfl, ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases (show (i : ℕ) = 2 * a + 1 ∨ 2 * a + 1 < i by omega) with h' | h'
    · have hk : ((i.succ : Fin (2 * e + 1 + 1)) : ℕ) = 2 * ((⟨a + 1, by omega⟩ : Fin (e + 1)) : ℕ) := by
        rw [Fin.val_succ]
        show (i : ℕ) + 1 = 2 * (a + 1)
        omega
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h', wd_even e j _ _ hk, wd_even e _ _ _ hk,
        wd_odd e _ i.castSucc (by rw [Fin.val_castSucc]; omega), Pi.add_apply, sh, if_neg (by simp), if_pos rfl,
        ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      refine wd_congr e _ _ _ fun k hk => ?_
      rw [Fin.val_succ] at hk
      rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]

theorem SZc_of : SZc := by
  intro q _ e
  unfold Cyc
  rw [zc_eq, map_sum]
  simp only [bd, Finsupp.linearCombination_single, one_smul]
  rw [Finset.sum_add_distrib, tail_sum, zero_add, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  refine alt_fin (A := ZMod q) e (fun p => ∑ j : Fin (e + 1) → ZMod q,
    (Finsupp.single (Fin.contractNth p (· * ·) (wd e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))) fun a ha => ?_
  refine Fintype.sum_equiv (Equiv.addRight (sh q e a)) _ _ fun j => ?_
  rw [contract_eq e a ha j]
  rfl

end LateralTheory.Q.SZcT

end
end


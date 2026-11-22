import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.CardMonicTwoRootsLe
section
open Polynomial Finset

noncomputable section

namespace PI.SqfDivDeg.W

open Classical

def rts {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Finset (ZMod g) :=
  univ.filter (fun c => f.IsRoot c)

theorem rt_one (g : ℕ) [Fact g.Prime] : Rt g 1 = Mon g 1 := by
  unfold Rt
  apply Finset.filter_true_of_mem
  intro p hp
  rw [mem_Mon] at hp
  exact exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hp.1.ne_zero, hp.2, Nat.cast_one])

theorem card_fib_ge {g : ℕ} [Fact g.Prime] (n : ℕ) (c : ZMod g) :
    g ^ n ≤ ((Mon g (n + 1)).filter (fun f => f.IsRoot c)).card := by
  rw [← card_Mon g n]
  apply Finset.card_le_card_of_injOn (fun h => (X - C c) * h)
  · intro h hh
    have hh' : h ∈ Mon g n := by simpa using hh
    rw [mem_Mon] at hh'
    have : (X - C c) * h ∈ (Mon g (n + 1)).filter (fun f => f.IsRoot c) := by
      rw [Finset.mem_filter, mem_Mon]
      refine ⟨⟨(monic_X_sub_C c).mul hh'.1, ?_⟩, ?_⟩
      · rw [(monic_X_sub_C c).natDegree_mul hh'.1, natDegree_X_sub_C, hh'.2]
        ring
      · simp [IsRoot]
    simpa using this
  · intro h1 _ h2 _ e
    exact mul_left_cancel₀ (X_sub_C_ne_zero c) e

theorem decomp2 {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]} {c d : ZMod g} (hcd : c ≠ d)
    (hc : f.IsRoot c) (hd : f.IsRoot d) :
    (X - C c) * ((X - C d) * ((f /ₘ (X - C c)) /ₘ (X - C d))) = f := by
  have h1 := mul_divByMonic_eq_iff_isRoot.mpr hc
  have hd1 : (f /ₘ (X - C c)).IsRoot d := by
    rw [← h1] at hd
    simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hd
    rcases hd with hd | hd
    · exact absurd (sub_eq_zero.mp hd).symm hcd
    · exact hd
  rw [mul_divByMonic_eq_iff_isRoot.mpr hd1, h1]

theorem card_monic_two_roots_le {g : ℕ} [Fact g.Prime] (n : ℕ) (c d : ZMod g) (hcd : c ≠ d) :
    ((Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d)).card ≤ g ^ n := by
  rw [← card_Mon g n]
  apply Finset.card_le_card_of_injOn (fun f => (f /ₘ (X - C c)) /ₘ (X - C d))
  · intro f hf
    have hf' : f ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf
    rw [Finset.mem_filter, mem_Mon] at hf'
    obtain ⟨⟨hm, hn⟩, hc, hd⟩ := hf'
    have e := decomp2 hcd hc hd
    set q := (f /ₘ (X - C c)) /ₘ (X - C d)
    have hm1 : ((X - C d) * q).Monic :=
      (monic_X_sub_C c).of_mul_monic_left (by rw [e]; exact hm)
    have hm2 : q.Monic := (monic_X_sub_C d).of_mul_monic_left hm1
    have hq : q ∈ Mon g n := by
      rw [mem_Mon]
      refine ⟨hm2, ?_⟩
      have := congrArg natDegree e
      rw [(monic_X_sub_C c).natDegree_mul hm1, (monic_X_sub_C d).natDegree_mul hm2,
        natDegree_X_sub_C, natDegree_X_sub_C, hn] at this
      omega
    simpa using hq
  · intro f1 hf1 f2 hf2 e
    have hf1' : f1 ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf1
    have hf2' : f2 ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf2
    rw [Finset.mem_filter] at hf1' hf2'
    have e1 := decomp2 hcd hf1'.2.1 hf1'.2.2
    have e2 := decomp2 hcd hf2'.2.1 hf2'.2.2
    simp only at e
    rw [← e1, ← e2, e]

theorem pt (k : ℕ) : 2 * k ≤ (k * k - k) + 2 * (if k = 0 then 0 else 1) := by
  match k with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
    have h : (k + 2) * (k + 2) - (k + 2) = (k + 2) * (k + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h]
    simp
    nlinarith

theorem sum_rts {g : ℕ} [Fact g.Prime] (S : Finset (ZMod g)[X]) :
    ∑ f ∈ S, (rts f).card = ∑ c : ZMod g, (S.filter (fun f => f.IsRoot c)).card := by
  simp only [rts, Finset.card_filter]
  exact Finset.sum_comm

theorem sum_offDiag {g : ℕ} [Fact g.Prime] (S : Finset (ZMod g)[X]) :
    ∑ f ∈ S, (rts f).offDiag.card =
      ∑ x ∈ (univ : Finset (ZMod g)).offDiag,
        (S.filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card := by
  have hs : ∀ f : (ZMod g)[X], (rts f).offDiag =
      (univ : Finset (ZMod g)).offDiag.filter (fun x => f.IsRoot x.1 ∧ f.IsRoot x.2) := by
    intro f
    ext x
    simp only [rts, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp only [hs, Finset.card_filter]
  exact Finset.sum_comm

theorem card_Rt_eq {g : ℕ} [Fact g.Prime] (n : ℕ) :
    (Rt g n).card = ∑ f ∈ Mon g n, (if (rts f).card = 0 then 0 else 1) := by
  rw [Rt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  have e : (∃ x, f.IsRoot x) ↔ (rts f).card ≠ 0 := by
    rw [Finset.card_ne_zero]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [rts, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [rts, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx⟩
  by_cases h : (rts f).card = 0
  · have : ¬ ∃ x, f.IsRoot x := fun hx => e.mp hx h
    rw [if_neg this, if_pos h]
  · rw [if_pos (e.mpr h), if_neg h]

theorem rootDense : RootDense := by
  intro g _ n hn
  obtain rfl | hn2 : n = 1 ∨ 2 ≤ n := by omega
  · rw [rt_one, card_Mon]
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpt : ∑ f ∈ Mon g (m + 2), 2 * (rts f).card ≤
      ∑ f ∈ Mon g (m + 2), ((rts f).offDiag.card + 2 * (if (rts f).card = 0 then 0 else 1)) := by
    refine Finset.sum_le_sum (fun f _ => ?_)
    rw [Finset.offDiag_card]
    exact pt _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← card_Rt_eq] at hpt
  have h1 : g * g ^ (m + 1) ≤ ∑ f ∈ Mon g (m + 2), (rts f).card := by
    rw [sum_rts]
    have := Finset.card_nsmul_le_sum (univ : Finset (ZMod g))
      (fun c => ((Mon g (m + 1 + 1)).filter (fun f => f.IsRoot c)).card) (g ^ (m + 1))
      (fun c _ => card_fib_ge (m + 1) c)
    simpa [ZMod.card] using this
  have h2 : ∑ f ∈ Mon g (m + 2), (rts f).offDiag.card ≤ (g * g - g) * g ^ m := by
    rw [sum_offDiag]
    have := Finset.sum_le_card_nsmul ((univ : Finset (ZMod g)).offDiag)
      (fun x => ((Mon g (m + 2)).filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card) (g ^ m)
      (fun x hx => card_monic_two_roots_le m x.1 x.2 (Finset.mem_offDiag.mp hx).2.2)
    simpa [Finset.offDiag_card, ZMod.card] using this
  have hB : (g * g - g) * g ^ m ≤ g * g * g ^ m := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have eA : g ^ (m + 2) = g * g * g ^ m := by ring
  have eA' : g * g ^ (m + 1) = g * g * g ^ m := by ring
  rw [eA]
  rw [eA'] at h1
  omega

end PI.SqfDivDeg.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.FibreNonempty
section
open Polynomial Finset

noncomputable section

namespace PI.SqfDivDeg.W

theorem second_pair {g : ℕ} [Fact g.Prime] {q h : (ZMod g)[X]} (hq : q.Monic) (hh : h.Monic)
    (hs : Squarefree (q * h)) {x y : ZMod g} (hx : q.IsRoot x) (hy : h.IsRoot y) :
    ((X - C y) * (q /ₘ (X - C x))).Monic ∧ ((X - C x) * (h /ₘ (X - C y))).Monic ∧
    ((X - C y) * (q /ₘ (X - C x))).natDegree = q.natDegree ∧
    ((X - C x) * (h /ₘ (X - C y))).natDegree = h.natDegree ∧
    ((X - C y) * (q /ₘ (X - C x))) * ((X - C x) * (h /ₘ (X - C y))) = q * h ∧
    (X - C y) * (q /ₘ (X - C x)) ≠ q := by
  have hq' : (X - C x) * (q /ₘ (X - C x)) = q := mul_divByMonic_eq_iff_isRoot.mpr hx
  have hh' : (X - C y) * (h /ₘ (X - C y)) = h := mul_divByMonic_eq_iff_isRoot.mpr hy
  have mq : (q /ₘ (X - C x)).Monic :=
    (monic_X_sub_C x).of_mul_monic_left (by rw [hq']; exact hq)
  have mh : (h /ₘ (X - C y)).Monic :=
    (monic_X_sub_C y).of_mul_monic_left (by rw [hh']; exact hh)
  have dq : q.natDegree = 1 + (q /ₘ (X - C x)).natDegree := by
    conv_lhs => rw [← hq']
    rw [(monic_X_sub_C x).natDegree_mul mq, natDegree_X_sub_C]
  have dh : h.natDegree = 1 + (h /ₘ (X - C y)).natDegree := by
    conv_lhs => rw [← hh']
    rw [(monic_X_sub_C y).natDegree_mul mh, natDegree_X_sub_C]
  refine ⟨(monic_X_sub_C y).mul mq, (monic_X_sub_C x).mul mh, ?_, ?_, ?_, ?_⟩
  · rw [(monic_X_sub_C y).natDegree_mul mq, natDegree_X_sub_C, dq]
  · rw [(monic_X_sub_C x).natDegree_mul mh, natDegree_X_sub_C, dh]
  · calc (X - C y) * (q /ₘ (X - C x)) * ((X - C x) * (h /ₘ (X - C y)))
        = ((X - C x) * (q /ₘ (X - C x))) * ((X - C y) * (h /ₘ (X - C y))) := by ring
      _ = q * h := by rw [hq', hh']
  · intro heq
    have hqy : (X - C y) ∣ q := ⟨_, heq.symm⟩
    have hhy : (X - C y) ∣ h := dvd_iff_isRoot.mpr hy
    exact not_isUnit_X_sub_C y (hs _ (mul_dvd_mul hqy hhy))

theorem fibre_nonempty {g r a : ℕ} [Fact g.Prime] (har : a ≤ r) {f : (ZMod g)[X]}
    (hf : PI.SqfLab.Eiv g r a f) :
    ∃ q h, q ∈ Mon g a ∧ h ∈ Mon g (r - a) ∧ q * h = f := by
  obtain ⟨⟨hmon, hdeg, -⟩, -, q, hqf, hqa⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; exact hf0 (zero_dvd_iff.mp hqf)
  obtain ⟨k, hk⟩ := hqf
  have hl : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  have m1 : (q * C (q.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hq0
  have d1 : (q * C (q.leadingCoeff)⁻¹).natDegree = a := by
    rw [natDegree_mul_C (inv_ne_zero hl), hqa]
  have e : (q * C (q.leadingCoeff)⁻¹) * (C q.leadingCoeff * k) = f := by
    rw [hk]
    calc q * C (q.leadingCoeff)⁻¹ * (C q.leadingCoeff * k)
        = q * (C ((q.leadingCoeff)⁻¹ * q.leadingCoeff)) * k := by rw [C_mul]; ring
      _ = q * k := by rw [inv_mul_cancel₀ hl, C_1, mul_one]
  have m2 : (C q.leadingCoeff * k).Monic := m1.of_mul_monic_left (by rw [e]; exact hmon)
  have d2 : (C q.leadingCoeff * k).natDegree = r - a := by
    have := m1.natDegree_mul m2
    rw [e, hdeg, d1] at this
    omega
  exact ⟨_, _, mem_Mon.mpr ⟨m1, d1⟩, mem_Mon.mpr ⟨m2, d2⟩, e⟩

theorem mainCount : MainCount := by
  intro g r _ a har T hT
  classical
  let P := Mon g a ×ˢ Mon g (r - a)
  let F : (ZMod g)[X] → Finset ((ZMod g)[X] × (ZMod g)[X]) :=
    fun f => P.filter (fun p => p.1 * p.2 = f)
  let G : (ZMod g)[X] × (ZMod g)[X] → Prop :=
    fun p => (∃ x : ZMod g, p.1.IsRoot x) ∧ (∃ y : ZMod g, p.2.IsRoot y)
  let b : (ZMod g)[X] × (ZMod g)[X] → ℝ := fun p => if G p then 1 / 2 else 1
  have bnn : ∀ p, 0 ≤ b p := fun p => by simp only [b]; split_ifs <;> norm_num
  have key : ∀ f ∈ T, (1 : ℝ) ≤ ∑ p ∈ F f, b p := by
    intro f hf
    obtain ⟨q, h, hq, hh, hqh⟩ := fibre_nonempty har (hT f hf)
    have hpq : (q, h) ∈ F f := by simp [F, P, hq, hh, hqh]
    by_cases hG : G (q, h)
    · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hG
      have hs : Squarefree (q * h) := hqh ▸ (hT f hf).2.1
      obtain ⟨m1, m2, d1, d2, e, ne⟩ :=
        second_pair (mem_Mon.mp hq).1 (mem_Mon.mp hh).1 hs hx hy
      have hp' : ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) ∈ F f := by
        simp only [F, P, mem_filter, mem_product, mem_Mon]
        exact ⟨⟨⟨m1, d1.trans (mem_Mon.mp hq).2⟩, ⟨m2, d2.trans (mem_Mon.mp hh).2⟩⟩,
          e.trans hqh⟩
      have hG' : G ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) :=
        ⟨⟨y, by simp⟩, ⟨x, by simp⟩⟩
      have hG0 : G (q, h) := ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hne : ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) ≠ (q, h) :=
        fun h' => ne (congrArg Prod.fst h')
      have hsub : ∑ p ∈ ({((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))),
          (q, h)} : Finset _), b p ≤ ∑ p ∈ F f, b p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact hp'
          · exact hpq
        · intro p _ _; exact bnn p
      rw [sum_pair hne] at hsub
      simp only [b, if_pos hG', if_pos hG0] at hsub
      linarith
    · have : b (q, h) ≤ ∑ p ∈ F f, b p :=
        single_le_sum (f := b) (fun p _ => bnn p) hpq
      simp only [b, if_neg hG] at this
      exact this
  have hdisj : Set.PairwiseDisjoint (↑T) F := by
    intro f _ f' _ hff'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [F, mem_filter] at hp hp'
    exact hff' (hp.2.symm.trans hp'.2)
  have h1 : (T.card : ℝ) ≤ ∑ p ∈ T.biUnion F, b p := by
    rw [sum_biUnion hdisj]
    calc (T.card : ℝ) = ∑ f ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum key
  have h2 : ∑ p ∈ T.biUnion F, b p ≤ ∑ p ∈ P, b p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨f, -, hpf⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp hpf).1
    · intro p _ _; exact bnn p
  have h3 : ∑ p ∈ P, b p = (P.card : ℝ) - ((P.filter G).card : ℝ) / 2 := by
    simp only [b]
    rw [sum_ite]
    simp only [sum_const, nsmul_eq_mul]
    have hc := card_filter_add_card_filter_not (s := P) (fun p => G p)
    have h' : ((P.filter G).card : ℝ) + ((P.filter (fun p => ¬ G p)).card : ℝ) = P.card := by
      exact_mod_cast hc
    linarith
  have h4 : P.filter G = Rt g a ×ˢ Rt g (r - a) := by
    ext ⟨q, h⟩
    simp only [P, G, Rt, mem_filter, mem_product]
    tauto
  have h5 : (P.card : ℝ) = (g : ℝ) ^ r := by
    simp only [P, card_product, card_Mon]
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [h4, h5, card_product] at h3
  push_cast at h3
  linarith

end PI.SqfDivDeg.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.SqfDivDegOf
section
open Polynomial

namespace PI.SqfDivDeg.W

theorem sqfDivDeg_of (hA : RootDense) (hB : MainCount) : PI.SqfDivDeg.Claim := by
  intro g r _ hr hg a ha1 ha2 T hT
  have h1 := hA g a ha1
  have h2 := hA g (r - a) (by omega)
  have h3 := hB g r a (by omega) T hT
  have e : (g : ℝ) ^ r = (g : ℝ) ^ a * (g : ℝ) ^ (r - a) := by
    rw [← pow_add]; congr 1; omega
  have h1' : ((g : ℝ) ^ a) ≤ 2 * ((Rt g a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((g : ℝ) ^ (r - a)) ≤ 2 * ((Rt g (r - a)).card : ℝ) := by exact_mod_cast h2
  have p1 : (0 : ℝ) ≤ (g : ℝ) ^ a := by positivity
  have p2 : (0 : ℝ) ≤ (g : ℝ) ^ (r - a) := by positivity
  have hm : (g : ℝ) ^ a * (g : ℝ) ^ (r - a) ≤
      (2 * ((Rt g a).card : ℝ)) * (2 * ((Rt g (r - a)).card : ℝ)) :=
    mul_le_mul h1' h2' p2 (by linarith)
  rw [e] at h3 ⊢
  nlinarith

end PI.SqfDivDeg.W
end


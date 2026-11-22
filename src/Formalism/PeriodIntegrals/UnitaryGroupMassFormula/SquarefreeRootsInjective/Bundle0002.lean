import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.CardLeSumOfCover
section
open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

def LS (g r n : ℕ) : Finset ℕ := n.primeFactors.filter (fun ℓ => ℓ ∉ BB r g)

def WA (g e j ℓ : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  (nthRoots ((g ^ j - 1) * Lp g e ℓ) (1 : Fbar g)).toFinset.filter
    (fun w => (minpoly (ZMod g) w).natDegree = e)

def YB (g e' : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  ((X ^ (g ^ e') - X : (Fbar g)[X]).roots.toFinset).filter
    (fun y => (minpoly (ZMod g) y).natDegree = e')

def XB (g e ℓ : ℕ) [Fact g.Prime] (y : Fbar g) : Finset (Fbar g) :=
  (nthRoots (Lp g e ℓ) ((primeToPart ℓ y) ^ Lp g e ℓ)).toFinset.filter
    (fun x => (minpoly (ZMod g) x).natDegree = e)

def SA (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2), ∑ ℓ ∈ LS g r (g ^ e - 1),
    (g ^ j - 1) * Lp g e ℓ * g ^ (r - e)

def SB (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
    g ^ e' * Lp g e ℓ * g ^ (r - e - e')

theorem lp_pos {g e ℓ : ℕ} (hℓ : ℓ.Prime) : 0 < Lp g e ℓ := pow_pos hℓ.pos _

theorem minpoly_monic' {g : ℕ} [Fact g.Prime] (w : Fbar g) : (minpoly (ZMod g) w).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral w)

def PA (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 2 r, ∃ j ∈ Finset.Icc 1 (e / 2),
    ∃ ℓ ∈ LS g r (g ^ e - 1), ∃ w ∈ WA g e j ℓ, minpoly (ZMod g) w ∣ f

def PB (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 1 r, ∃ e' ∈ Finset.Icc 1 (min e (r - e)),
    ∃ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∃ y ∈ YB g e', ∃ x ∈ XB g e ℓ y,
      minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f

theorem g_pow_sub_one_ne {g e : ℕ} (hg2 : 1 < g) (he : 1 ≤ e) : g ^ e - 1 ≠ 0 := by
  have := Nat.one_lt_pow (by omega : e ≠ 0) hg2
  omega

theorem caseA_PA {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseA g r ℓ f) : PA g r f := by
  have hg2 : 1 < g := hg.out.one_lt
  obtain ⟨e, j, w, he2, her, hj1, hj2, hdv, hdeg, hdvd, hpow⟩ := h
  refine ⟨e, ?_, j, ?_, ℓ, ?_, w, ?_, hdvd⟩
  · exact Finset.mem_Icc.2 ⟨he2, her⟩
  · exact Finset.mem_Icc.2 ⟨hj1, by omega⟩
  · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hℓ, hdv, g_pow_sub_one_ne hg2 (by omega)⟩, hB⟩
  · refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_nthRoots ?_).2 hpow), hdeg⟩
    have : 1 ≤ g ^ j - 1 := by
      have := Nat.one_lt_pow (by omega : j ≠ 0) hg2
      omega
    exact Nat.mul_pos this (lp_pos hℓ)

theorem caseB_PB {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseB g r ℓ f) : PB g r f := by
  have hg2 : 1 < g := hg.out.one_lt
  obtain ⟨e, e', x, y, he', he'e, hsum, hdv, hdx, hdy, hdvd, hy, hx⟩ := h
  refine ⟨e, ?_, e', ?_, ℓ, ?_, y, ?_, x, ?_, hdvd⟩
  · exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · exact Finset.mem_Icc.2 ⟨he', by omega⟩
  · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
      ⟨hℓ, hdv, Nat.mul_ne_zero (g_pow_sub_one_ne hg2 (by omega)) (g_pow_sub_one_ne hg2 he')⟩, hB⟩
  · refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ?_, hdy⟩
    have hM : 1 < g ^ e' := Nat.one_lt_pow (by omega) hg2
    rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hM)]
    simp [hy]
  · exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_nthRoots (lp_pos hℓ)).2 hx), hdx⟩

theorem cardA (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PA g r)).card ≤ SA g r := by
  calc (T.filter (PA g r)).card ≤ ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2),
      ∑ ℓ ∈ LS g r (g ^ e - 1), ∑ w ∈ WA g e j ℓ,
        (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 2 r).biUnion fun e =>
          (Finset.Icc 1 (e / 2)).biUnion fun j => (LS g r (g ^ e - 1)).biUnion fun ℓ =>
            (WA g e j ℓ).biUnion fun w => T.filter (fun f => minpoly (ZMod g) w ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, j, hj, ℓ, hℓ, w, hw, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, j, hj, ℓ, hℓ, w, hw, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SA g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun ℓ _ => ?_
        calc ∑ w ∈ WA g e j ℓ, (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card
            ≤ ∑ w ∈ WA g e j ℓ, g ^ (r - e) := by
              refine Finset.sum_le_sum fun w hw => ?_
              have h1 := divCount r T hmon _ (minpoly_monic' w)
              have h2 : (minpoly (ZMod g) w).natDegree = e := (Finset.mem_filter.1 hw).2
              rw [h2] at h1
              exact h1
          _ = (WA g e j ℓ).card * g ^ (r - e) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (g ^ j - 1) * Lp g e ℓ * g ^ (r - e) :=
              Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))

theorem cardB (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PB g r)).card ≤ SB g r := by
  have hg2 : 1 < g := hg.out.one_lt
  calc (T.filter (PB g r)).card ≤ ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)),
      ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
        (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 1 r).biUnion fun e =>
          (Finset.Icc 1 (min e (r - e))).biUnion fun e' => (LS g r ((g ^ e - 1) * (g ^ e' - 1))).biUnion fun ℓ =>
            (YB g e').biUnion fun y => (XB g e ℓ y).biUnion fun x =>
              T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, e', he', ℓ, hℓ, y, hy, x, hx, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, e', he', ℓ, hℓ, y, hy, x, hx, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e' _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SB g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun e' he' =>
          Finset.sum_le_sum fun ℓ _ => ?_
        have he1 : 1 ≤ e' := (Finset.mem_Icc.1 he').1
        calc ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
              (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card
            ≤ ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y, g ^ (r - e - e') := by
              refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun x hx => ?_
              have h1 := divCount r T hmon _ ((minpoly_monic' x).mul (minpoly_monic' y))
              have h2 : (minpoly (ZMod g) x * minpoly (ZMod g) y).natDegree = e + e' := by
                rw [(minpoly_monic' x).natDegree_mul (minpoly_monic' y),
                  (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
              rw [h2] at h1
              rw [Nat.sub_sub]
              exact h1
          _ = ∑ y ∈ YB g e', (XB g e ℓ y).card * g ^ (r - e - e') := by
              simp only [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ y ∈ YB g e', Lp g e ℓ * g ^ (r - e - e') :=
              Finset.sum_le_sum fun y _ => Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))
          _ = (YB g e').card * (Lp g e ℓ * g ^ (r - e - e')) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ g ^ e' * (Lp g e ℓ * g ^ (r - e - e')) :=
              Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans
                (card_roots_X_pow_sub_X_le _ (Nat.one_lt_pow (by omega) hg2)))
          _ = g ^ e' * Lp g e ℓ * g ^ (r - e - e') := by rw [mul_assoc]

theorem card_le_SA_SB (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, IsLab g r f ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧
      (CaseA g r ℓ f ∨ CaseB g r ℓ f)) :
    T.card ≤ SA g r + SB g r := by
  have hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r := fun f hf => ⟨(hT f hf).1.1, (hT f hf).1.2.1⟩
  have hcov : T ⊆ T.filter (PA g r) ∪ T.filter (PB g r) := by
    intro f hf
    obtain ⟨_, ℓ, hℓ, hB, hAB⟩ := hT f hf
    rcases hAB with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hf, caseA_PA hℓ hB h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hf, caseB_PB hℓ hB h⟩)
  calc T.card ≤ (T.filter (PA g r) ∪ T.filter (PB g r)).card := Finset.card_le_card hcov
    _ ≤ (T.filter (PA g r)).card + (T.filter (PB g r)).card := Finset.card_union_le _ _
    _ ≤ SA g r + SB g r := Nat.add_le_add (cardA g r T hmon) (cardB g r T hmon)

end PI.SqfRootsInj.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.WitMain
section
open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab

section
variable {g : ℕ} [Fact g.Prime]

theorem root_facts {r : ℕ} {f : (ZMod g)[X]} (hf : IsLab g r f) {x : Fbar g}
    (hx : x ∈ rootsBar f) :
    x ≠ 0 ∧ minpoly (ZMod g) x ∣ f ∧ (minpoly (ZMod g) x).natDegree ≤ r ∧
      1 ≤ (minpoly (ZMod g) x).natDegree := by
  obtain ⟨hmon, hdeg, hc0⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots'] at hx
    rw [← eval_map_algebraMap]
    exact hx.2
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hdvd := minpoly.dvd (ZMod g) x hroot
  refine ⟨?_, hdvd, ?_, minpoly.natDegree_pos hint⟩
  · rintro rfl
    apply hc0
    have h0 := coeff_zero_eq_aeval_zero' (A := Fbar g) f
    rw [hroot] at h0
    exact (algebraMap (ZMod g) (Fbar g)).injective (by rw [h0, map_zero])
  · rw [← hdeg]
    exact natDegree_le_of_dvd hdvd hf0

theorem pow_pred_eq_one' {K : Type*} [Field K] {x : K} (hx : x ≠ 0) {q : ℕ} (hq : 1 ≤ q)
    (h : x ^ q = x) : x ^ (q - 1) = 1 := by
  have h2 : x ^ (q - 1) * x = 1 * x := by rw [← pow_succ, Nat.sub_add_cancel hq, h, one_mul]
  exact mul_right_cancel₀ hx h2

theorem two_mul_le_of_dvd_ne {J E : ℕ} (hd : J ∣ E) (hne : J ≠ E) (hE : 1 ≤ E) : 2 * J ≤ E := by
  obtain ⟨c, hc⟩ := hd
  subst hc
  rcases Nat.lt_or_ge c 2 with h | h
  · interval_cases c
    · omega
    · exact absurd (mul_one J).symm hne
  · nlinarith

theorem orderOf_dvd_pow_sub_one {x : Fbar g} (hx0 : x ≠ 0) {e : ℕ}
    (he : (minpoly (ZMod g) x).natDegree = e) (he1 : 1 ≤ e) :
    g ^ e - 1 ≠ 0 ∧ orderOf x ∣ g ^ e - 1 := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hxe : x ^ (g ^ e) = x := he ▸ pow_card_minpoly x
  refine ⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hg), ?_⟩
  exact orderOf_dvd_of_pow_eq_one (pow_pred_eq_one' hx0 (Nat.one_le_pow _ _ (by omega)) hxe)

theorem caseB_of {r ℓ : ℕ} (hℓ : ℓ.Prime) {f : (ZMod g)[X]} (hf : IsLab g r f)
    {x y : Fbar g} (hx : x ∈ rootsBar f) (hy : y ∈ rootsBar f) (hxy : x ≠ y)
    (hp : primeToPart ℓ x = primeToPart ℓ y)
    (hne : minpoly (ZMod g) x ≠ minpoly (ZMod g) y)
    (hle : (minpoly (ZMod g) y).natDegree ≤ (minpoly (ZMod g) x).natDegree) :
    CaseB g r ℓ f := by
  obtain ⟨hx0, hxd, -, hx1⟩ := root_facts hf hx
  obtain ⟨hy0, hyd, -, hy1⟩ := root_facts hf hy
  have hxint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hyint : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
  have hcop : IsCoprime (minpoly (ZMod g) x) (minpoly (ZMod g) y) := by
    refine (Irreducible.coprime_iff_not_dvd (minpoly.irreducible hxint)).2 fun h => hne ?_
    exact eq_of_monic_of_associated (minpoly.monic hxint) (minpoly.monic hyint)
      ((minpoly.irreducible hxint).associated_of_dvd (minpoly.irreducible hyint) h)
  have hprod : minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f := hcop.mul_dvd hxd hyd
  have hdeg : (minpoly (ZMod g) x).natDegree + (minpoly (ZMod g) y).natDegree ≤ r := by
    rw [← hf.2.1, ← natDegree_mul (minpoly.ne_zero hxint) (minpoly.ne_zero hyint)]
    exact natDegree_le_of_dvd hprod hf.1.ne_zero
  obtain ⟨hNe, hox⟩ := orderOf_dvd_pow_sub_one hx0 rfl hx1
  obtain ⟨hNe', hoy⟩ := orderOf_dvd_pow_sub_one hy0 rfl hy1
  refine ⟨_, _, x, y, hy1, hle, hdeg, ?_, rfl, rfl, hprod, pow_card_minpoly y, ?_⟩
  · by_contra hnd
    have hv := padicValNat.eq_zero_of_not_dvd hnd
    have h1 := pow_eq_part_pow_of_dvd ℓ hℓ x _ (mul_ne_zero hNe hNe')
      (dvd_mul_of_dvd_left hox _)
    have h2 := pow_eq_part_pow_of_dvd ℓ hℓ y _ (mul_ne_zero hNe hNe')
      (dvd_mul_of_dvd_right hoy _)
    rw [hv, pow_zero, pow_one, pow_one] at h1 h2
    exact hxy (by rw [h1, h2, hp])
  · unfold Lp
    rw [← hp]
    exact pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox

theorem caseA_of {r ℓ : ℕ} (hℓ : ℓ.Prime) {f : (ZMod g)[X]} (hf : IsLab g r f)
    {x y : Fbar g} (hx : x ∈ rootsBar f) (hy : y ∈ rootsBar f) (hxy : x ≠ y)
    (hp : primeToPart ℓ x = primeToPart ℓ y)
    (heq : minpoly (ZMod g) x = minpoly (ZMod g) y) :
    CaseA g r ℓ f := by
  obtain ⟨hx0, hxd, hxr, hx1⟩ := root_facts hf hx
  obtain ⟨hy0, -, -, -⟩ := root_facts hf hy
  have hxint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  obtain ⟨hNe, hox⟩ := orderOf_dvd_pow_sub_one hx0 rfl hx1
  obtain ⟨-, hoy⟩ := orderOf_dvd_pow_sub_one hy0 (congrArg natDegree heq.symm) hx1
  have hxL := pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox
  have hyL := pow_eq_part_pow_of_dvd ℓ hℓ y _ hNe hoy
  have htt : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ =
      y ^ Lp g (minpoly (ZMod g) x).natDegree ℓ := by
    unfold Lp; rw [hxL, hyL, hp]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ZMod g) (E := Fbar g)).1 heq.symm
  replace hσ : σ x = y := hσ
  have hσt : σ (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) =
      x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ := by
    rw [map_pow, hσ, htt]
  have hxnot : x ∉ IntermediateField.adjoin (ZMod g)
      {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} := by
    intro hmem
    obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (ZMod g) x).1 hmem
    have hfix : σ x = x := by
      rw [hpq, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hσt]
    exact hxy (hfix.symm.trans hσ)
  have htint : IsIntegral (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) :=
    Algebra.IsIntegral.isIntegral _
  have hle : IntermediateField.adjoin (ZMod g) {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} ≤
      IntermediateField.adjoin (ZMod g) {x} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self (ZMod g) x) _
  haveI := IntermediateField.adjoin.finiteDimensional hxint
  have hdiv : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ∣
      (minpoly (ZMod g) x).natDegree := by
    have h := IntermediateField.finrank_dvd_of_le_right hle
    rwa [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint] at h
  have hjne : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≠
      (minpoly (ZMod g) x).natDegree := by
    intro hEq
    apply hxnot
    have hEq2 := IntermediateField.eq_of_le_of_finrank_eq hle
      (by rw [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint, hEq])
    rw [hEq2]
    exact IntermediateField.mem_adjoin_simple_self _ x
  have hj1 := minpoly.natDegree_pos htint
  have h2j : 2 * (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≤
      (minpoly (ZMod g) x).natDegree := by
    exact two_mul_le_of_dvd_ne hdiv hjne hx1
  have ht0 : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ ≠ 0 := pow_ne_zero _ hx0
  have htj := pow_pred_eq_one' ht0 (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos)
    (pow_card_minpoly (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ))
  refine ⟨_, _, x, by omega, hxr, hj1, h2j, ?_, rfl, hxd, ?_⟩
  · by_contra hnd
    have hv := padicValNat.eq_zero_of_not_dvd hnd
    rw [hv, pow_zero, pow_one, pow_one] at hxL hyL
    exact hxy (by rw [hxL, hyL, hp])
  · rw [mul_comm, pow_mul]
    exact htj

end

theorem counted_labels_have_witness : Witness := by
  intro g r _ f hf
  obtain ⟨hlab, -, hnot⟩ := hf
  push Not at hnot
  obtain ⟨ℓ, hℓ, hBB, x, hx, y, hy, hp, hxy⟩ := hnot
  refine ⟨ℓ, hℓ, hBB, ?_⟩
  by_cases heq : minpoly (ZMod g) x = minpoly (ZMod g) y
  · exact Or.inl (caseA_of hℓ hlab hx hy hxy hp heq)
  · right
    rcases le_total (minpoly (ZMod g) y).natDegree (minpoly (ZMod g) x).natDegree with h | h
    · exact caseB_of hℓ hlab hx hy hxy hp heq h
    · exact caseB_of hℓ hlab hy hx (Ne.symm hxy) hp.symm (Ne.symm heq) h

end PI.SqfRootsInj.W
end
end


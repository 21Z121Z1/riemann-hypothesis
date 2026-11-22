import Mathlib
import Formalism.TruncatedSeriesCounting.Bundle0001
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound
import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle0003

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ArcExp
section
namespace Formalism.TruncatedSeriesCounting.X

theorem arc_exponential_identity : ArcExp := by
  intro r σ κ G j' ell hr hσ hκ hG hj
  have hj' : (j' : ℝ) ≤ ell := by exact_mod_cast hj
  have hjG : (j' : ℝ) * G ≤ ell * G := mul_le_mul_of_nonneg_right hj' hG
  have hell : 0 ≤ (ell : ℝ) * G := mul_nonneg (Nat.cast_nonneg _) hG
  rcases le_total (r + κ) (2 * σ + 2 * j' * G + 1) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColTwoStep
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

private lemma comap_subtype_span_sup_eq_span_range_sup {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (Z J : Submodule O M) (s : Finset M) (hs : ∀ x ∈ s, x ∈ Z) :
    (Submodule.span O (s : Set M) ⊔ J).comap Z.subtype =
      Submodule.span O (Set.range fun x : s => (⟨x, hs x x.2⟩ : Z)) ⊔ J.comap Z.subtype := by
  apply Submodule.map_injective_of_injective Z.injective_subtype
  have hle : Submodule.span O (s : Set M) ≤ Z := Submodule.span_le.2 fun x hx => hs x hx
  have hr : Set.range (⇑Z.subtype ∘ fun x : s => (⟨x, hs x x.2⟩ : Z)) = (s : Set M) := by
    ext y
    simp
  rw [Submodule.map_sup, Submodule.map_span, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    ← Set.range_comp, hr, inf_comm Z, sup_inf_assoc_of_le J hle, inf_comm J Z]

theorem length_quotient_le_of_two_step : ColTwoStep := by
  unfold ColTwoStep
  intro O M _ _ _ ℓ g g₀ e e' Z I s s₀ hIZ hs hs₀ hs₀Z hspan hZ hI
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => by
    rw [← hspan]
    exact Submodule.mem_sup_left (Submodule.subset_span hx)
  have hs₀Z' : ∀ x ∈ s₀, x ∈ Z := fun x hx => hs₀Z hx
  have hIT : I.comap Z.subtype ≤ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    Submodule.comap_mono le_sup_right
  let N := ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ
  have hsplit : Module.length O (Z ⧸ I.comap Z.subtype) =
      Module.length O N + Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) :=
    Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hQN : Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) =
      Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) :=
    (Submodule.quotientQuotientEquivQuotient _ _ hIT).length_eq
  let q : s₀ → Z ⧸ I.comap Z.subtype := fun x => (I.comap Z.subtype).mkQ ⟨x, hs₀Z' x x.2⟩
  have hNq : N = Submodule.span O (Set.range q) := by
    show ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ = _
    rw [comap_subtype_span_sup_eq_span_range_sup Z I s₀ hs₀Z', Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
      Submodule.map_span, ← Set.range_comp]
    rfl
  let v : s₀ → N := fun x => ⟨q x, by rw [hNq]; exact Submodule.subset_span ⟨x, rfl⟩⟩
  have hv_top : Submodule.span O (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hNq.symm
  have hv_kill : ∀ x, ((ℓ : O) ^ e') • v x = 0 := by
    intro x
    apply Subtype.ext
    show ((ℓ : O) ^ e') • q x = 0
    simp only [q, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e') • (x : M) ∈ I
    have h := hI x (Submodule.subset_span x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hN : Module.length O N ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span v ((ℓ : O) ^ e') hv_top hv_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e'
    calc Module.length O N ≤ (Fintype.card s₀ : ℕ∞) *
          Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e'}) := h1
      _ ≤ (g₀ : ℕ∞) * ((e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs₀) h2
      _ = _ := by ring
  let w : s → Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    fun x => ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⟨x, hsZ x x.2⟩
  have hw_top : Submodule.span O (Set.range w) = ⊤ := by
    have htop : (⊤ : Submodule O Z) = Submodule.span O (Set.range fun x : s => (⟨x, hsZ x x.2⟩ : Z)) ⊔
        I.comap Z.subtype := by
      rw [← comap_subtype_span_sup_eq_span_range_sup Z I s hsZ, hspan, Submodule.comap_subtype_self]
    have hmt : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⊤ = ⊤ := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    have hbot : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ
        (I.comap Z.subtype) = ⊥ :=
      le_bot_iff.1 ((Submodule.map_mono hIT).trans (Submodule.mkQ_map_self _).le)
    rw [← hmt, htop, Submodule.map_sup, hbot, sup_bot_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  have hw_kill : ∀ x, ((ℓ : O) ^ e) • w x = 0 := by
    intro x
    simp only [w, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e) • (x : M) ∈ Submodule.span O (s₀ : Set M) ⊔ I
    have h := hZ x (hsZ x x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hZT : Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) ≤
      (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span w ((ℓ : O) ^ e) hw_top hw_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e
    calc _ ≤ (Fintype.card s : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e}) := h1
      _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs) h2
      _ = _ := by ring
  rw [hsplit, hQN]
  calc _ ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add hN hZT
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CountBd
section
noncomputable section

open Classical

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

open Formalism.WachCohomologyFacts

private lemma mem_cl {h η : ℕ} {U : Multiset ℤ} {u : ℤ} (hu : u ∈ U) (hc : u < (h : ℤ) - η) :
    u ∈ V2.ClN false h η U := by
  rw [V2.ClN, Multiset.mem_filter]
  refine ⟨hu, ?_⟩
  unfold V2.InWinN
  simp only [Bool.false_eq_true, if_false]
  omega

private lemma t3 {ℓ h η : ℕ} {σ : ℤ} {U : Multiset ℤ} (hT3 : V2.ResidueAvoidance ℓ false h η σ U) {u : ℤ}
    (hu : u ∈ U) (hc : u < (h : ℤ) - η) (k : ℤ) (hk1 : -2 * σ - 2 ≤ k)
    (hk2 : k ≤ (η : ℤ) + 2 * σ + 3) : ((((h : ℤ) - u : ℤ)) : ZMod ℓ) ≠ ((k : ℤ) : ZMod ℓ) := by
  have := hT3 u (mem_cl hu hc) k hk1 hk2
  simpa only [Bool.false_eq_true, if_false] using this

private lemma tele {ℓ : ℕ} (f g M : ZMod ℓ → ℕ) (hrel : ∀ x, f x + M (x + 1) = g x + M x)
    (a : ℤ) (k : ℕ) :
    (∑ n ∈ Finset.Icc a (a - 1 + k), f (((n : ℤ)) : ZMod ℓ)) + M ((((a + k : ℤ))) : ZMod ℓ) =
      (∑ n ∈ Finset.Icc a (a - 1 + k), g (((n : ℤ)) : ZMod ℓ)) + M (((a : ℤ)) : ZMod ℓ) := by
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ k ih =>
    have hs : Finset.Icc a (a - 1 + ((k + 1 : ℕ) : ℤ)) = insert (a + k) (Finset.Icc a (a - 1 + k)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    have hn : a + k ∉ Finset.Icc a (a - 1 + k) := by rw [Finset.mem_Icc]; omega
    rw [hs, Finset.sum_insert hn, Finset.sum_insert hn]
    have e1 : ((((a + ((k + 1 : ℕ) : ℤ)) : ℤ)) : ZMod ℓ) = ((((a + k : ℤ))) : ZMod ℓ) + 1 := by
      push_cast; ring
    rw [e1]
    have := hrel ((((a + k : ℤ))) : ZMod ℓ)
    omega

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CutsExist
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

namespace ClusterCuts

variable (j : ℕ) (th : ℤ → Prop) [DecidablePred th]

def Step (x y : ℤ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ j → ¬ th (x + i)) ∧ (j : ℤ) ≤ y - x ∧ y - x ≤ 3 * j + 1 ∧
    ((Finset.Ioc x y).filter th).card ≤ 2

def Chain (a b : ℤ) : Prop :=
  ∃ (m : ℕ) (c : ℕ → ℤ), 1 ≤ m ∧ c 0 = a ∧ c m = b ∧ ∀ k < m, Step j th (c k) (c (k + 1))

def ClustersZ : Prop :=
  ∀ t : ℤ, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k))

variable {j th}

lemma chain_of_step {a b : ℤ} (h : Step j th a b) : Chain j th a b := by
  refine ⟨1, fun k => if k = 0 then a else b, le_rfl, by simp, by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simpa using h

lemma chain_trans {a b d : ℤ} (h1 : Chain j th a b) (h2 : Chain j th b d) :
    Chain j th a d := by
  obtain ⟨m1, c1, hm1, h10, h1m, hs1⟩ := h1
  obtain ⟨m2, c2, hm2, h20, h2m, hs2⟩ := h2
  refine ⟨m1 + m2, fun k => if k ≤ m1 then c1 k else c2 (k - m1), by omega, ?_, ?_, ?_⟩
  · simp [h10]
  · have hn : ¬ (m1 + m2 ≤ m1) := by omega
    simp only [hn, if_false]
    rw [Nat.add_sub_cancel_left]
    exact h2m
  · intro k hk
    by_cases hk1 : k + 1 ≤ m1
    · have hk0 : k ≤ m1 := by omega
      simp only [hk0, hk1, if_true]
      exact hs1 k (by omega)
    · by_cases hkm : k = m1
      · subst hkm
        simp only [le_refl, if_true, hk1, if_false]
        rw [h1m, ← h20, show k + 1 - k = 0 + 1 by omega]
        exact hs2 0 hm2
      · have hk0 : ¬ k ≤ m1 := by omega
        simp only [hk0, hk1, if_false]
        rw [show k + 1 - m1 = (k - m1) + 1 by omega]
        exact hs2 (k - m1) (by omega)

lemma fill (hj : 1 ≤ j) (s : ℕ) : ∀ (a e : ℤ), j ≤ s →
    (∀ i : ℤ, a < i → i ≤ a + s → ¬ th i) → a + s ≤ e → e ≤ a + s + j + 1 →
    ((Finset.Ioc (a + s) e).filter th).card ≤ 2 → Chain j th a e := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a e hs hfree hae hea hcard
    by_cases h2 : s < 2 * j
    · apply chain_of_step
      refine ⟨?_, by omega, by omega, ?_⟩
      · intro i hi1 hij
        apply hfree <;> omega
      · calc ((Finset.Ioc a e).filter th).card
            ≤ ((Finset.Ioc (a + s) e).filter th).card := by
              apply Finset.card_le_card
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_Ioc] at hi ⊢
              refine ⟨⟨?_, hi.1.2⟩, hi.2⟩
              by_contra hc
              push Not at hc
              exact hfree i hi.1.1 hc hi.2
          _ ≤ 2 := hcard
    · push Not at h2
      apply chain_trans (b := a + j)
      · apply chain_of_step
        refine ⟨?_, by omega, by omega, ?_⟩
        · intro i hi1 hij
          apply hfree <;> omega
        · have he : (Finset.Ioc a (a + j)).filter th = ∅ := by
            apply Finset.filter_false_of_mem
            intro i hi
            simp only [Finset.mem_Ioc] at hi
            exact hfree i hi.1 (by omega)
          rw [he]
          simp
      · have hsj : ((s - j : ℕ) : ℤ) = (s : ℤ) - j := by
          rw [Nat.cast_sub (by omega)]
        have hpt : a + (j : ℤ) + ((s - j : ℕ) : ℤ) = a + s := by rw [hsj]; ring
        apply ih (s - j) (by omega) (a + j) e (by omega)
        · intro i hi1 hi2
          exact hfree i (by omega) (by rw [hpt] at hi2; exact hi2)
        · rw [hpt]; exact hae
        · rw [hpt]; exact hea
        · rw [hpt]; exact hcard

lemma pair (hC : ClustersZ j th) {f g : ℤ} (hf : th f) (hg : th g) (hfg : f < g)
    (hgf : g ≤ f + j) :
    (∀ i : ℤ, f < i → i < g → ¬ th i) ∧ (∀ i : ℤ, g < i → i ≤ g + j → ¬ th i) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = g - f := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  have hgk : g - (k : ℤ) = f := by omega
  rcases hC g hg with h1 | ⟨d, hd1, hdj, _hgd, hrest⟩
  · exact absurd (by rw [hgk]; exact hf) (h1 k (by omega) (by omega))
  have hkd : k = d := by
    by_contra hne
    exact hrest k (by omega) (by omega) hne (by rw [hgk]; exact hf)
  constructor
  · intro i hi1 hi2 hi
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k' : ℤ) = g - i := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    exact hrest k' (by omega) (by omega) (by omega) (by rw [show g - (k' : ℤ) = i by omega]; exact hi)
  · intro h hh1 hh2 hh
    obtain ⟨k'', hk''⟩ : ∃ k'' : ℕ, (k'' : ℤ) = h - g := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    have hhk : h - (k'' : ℤ) = g := by omega
    rcases hC h hh with h1' | ⟨d', hd1', hdj', _hhd, hrest'⟩
    · exact h1' k'' (by omega) (by omega) (by rw [hhk]; exact hg)
    have hkd' : k'' = d' := by
      by_contra hne
      exact hrest' k'' (by omega) (by omega) hne (by rw [hhk]; exact hg)
    obtain ⟨k3, hk3⟩ : ∃ k3 : ℕ, (k3 : ℤ) = h - f := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    exact hrest' k3 (by omega) (by omega) (by omega) (by rw [show h - (k3 : ℤ) = f by omega]; exact hf)

lemma cluster_chain (hC : ClustersZ j th) (hj : 1 ≤ j) (B : ℤ) (hB : th B)
    (hBl : ∀ i : ℤ, B < i → i ≤ B + j → ¬ th i) :
    ∀ (N : ℕ) (a : ℤ), B - a ≤ N → a < B → (∀ i : ℤ, a < i → i ≤ a + j → ¬ th i) →
      Chain j th a B := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a hN haB hfree
    have hex : ∃ k : ℕ, th (a + 1 + k) :=
      ⟨(B - a - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; convert hB using 1; ring⟩
    set k0 := Nat.find hex with hk0
    have hfth : th (a + 1 + k0) := Nat.find_spec hex
    have hkB : k0 ≤ (B - a - 1).toNat :=
      Nat.find_min' hex (by rw [Int.toNat_of_nonneg (by omega)]; convert hB using 1; ring)
    have hkB' : a + 1 + (k0 : ℤ) ≤ B := by
      have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ B - a - 1 by omega)
      omega
    have hmin : ∀ i : ℤ, a < i → i < a + 1 + k0 → ¬ th i := by
      intro i hi1 hi2 hi
      obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k' : ℤ) = i - a - 1 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
      have hlt : k' < k0 := by omega
      exact Nat.find_min hex hlt (by rw [show a + 1 + (k' : ℤ) = i by omega]; exact hi)
    set f : ℤ := a + 1 + k0 with hfdef
    have hfa : a + j < f := by
      by_contra hc
      push Not at hc
      exact hfree f (by omega) hc hfth
    obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = f - 1 - a := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    have hsfree : ∀ i : ℤ, a < i → i ≤ a + s → ¬ th i := fun i h1 h2 => hmin i h1 (by omega)

    have cont : ∀ e : ℤ, a < e → e ≤ B → (∀ i : ℤ, e < i → i ≤ e + j → ¬ th i) →
        Chain j th a e → Chain j th a B := by
      intro e hae heB hel hc
      rcases eq_or_lt_of_le heB with h | h
      · rw [← h]; exact hc
      · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = B - e := ⟨_, Int.toNat_of_nonneg (by omega)⟩
        exact chain_trans hc (ih N' (by omega) e (by omega) h hel)
    by_cases hl : ∀ i : ℤ, f < i → i ≤ f + j → ¬ th i
    · apply cont f (by omega) hkB' hl
      apply fill hj s a f (by omega) hsfree (by omega) (by omega)
      calc ((Finset.Ioc (a + s) f).filter th).card ≤ (Finset.Ioc (a + s) f).card :=
            Finset.card_filter_le _ _
        _ = 1 := by rw [Int.card_Ioc, show f - (a + s) = 1 by omega]; rfl
        _ ≤ 2 := by norm_num
    · push Not at hl
      obtain ⟨g, hfg, hgf, hg⟩ := hl
      obtain ⟨hmid, hgl⟩ := pair hC hfth hg hfg hgf
      have hgB : g ≤ B := by
        by_contra hc
        push Not at hc
        rcases eq_or_lt_of_le hkB' with h | h
        · exact hBl g (by omega) (by omega) hg
        · exact hmid B h hc hB
      apply cont g (by omega) hgB hgl
      apply fill hj s a g (by omega) hsfree (by omega) (by omega)
      calc ((Finset.Ioc (a + s) g).filter th).card ≤ ({f, g} : Finset ℤ).card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_Ioc] at hi
            simp only [Finset.mem_insert, Finset.mem_singleton]
            by_contra hc
            push Not at hc
            exact hmid i (by omega) (lt_of_le_of_ne hi.1.2 hc.2) hi.2
        _ ≤ 2 := Finset.card_le_two

lemma main (n : ℕ) (hj : 1 ≤ j) (hn : j + 1 ≤ n) (hper : ∀ i : ℤ, th (i + n) ↔ th i)
    (hC : ClustersZ j th) : ∃ a : ℤ, Chain j th a (a + n) := by
  by_cases hex : ∃ t : ℤ, th t
  · obtain ⟨t0, ht0⟩ := hex
    obtain ⟨t, ht, htl⟩ : ∃ t : ℤ, th t ∧ ∀ i : ℤ, t < i → i ≤ t + j → ¬ th i := by
      by_cases hl : ∀ i : ℤ, t0 < i → i ≤ t0 + j → ¬ th i
      · exact ⟨t0, ht0, hl⟩
      · push Not at hl
        obtain ⟨g, h1, h2, hg⟩ := hl
        exact ⟨g, hg, (pair hC ht0 hg h1 h2).2⟩
    refine ⟨t, cluster_chain hC hj (t + n) ((hper t).2 ht) ?_ n t (by omega) (by omega) htl⟩
    intro i hi1 hi2 hi
    have : th (i - n) := (hper (i - n)).1 (by rw [sub_add_cancel]; exact hi)
    exact htl (i - n) (by omega) (by omega) this
  · push Not at hex
    refine ⟨0, fill hj n 0 (0 + n) (by omega) (fun i _ _ => hex i) (by omega) (by omega) ?_⟩
    rw [Finset.filter_false_of_mem (fun i _ => hex i)]
    simp

end ClusterCuts

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LengthQuotientLeOfPowSMul
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

theorem length_quotient_le_of_pow_smul : LengthQuotientLeOfPowSMul := by
  intro O _ _ _ M _ _ _ _ ℓ e e' FFs J h1 h2
  set A := FFs ⊔ Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M) with hA
  have hx : ∀ x ∈ A, ℓ ^ e • x ∈ J := by
    intro x hxA
    obtain ⟨f, hf, m, hm, rfl⟩ := Submodule.mem_sup.1 hxA
    rw [smul_add]
    exact J.add_mem (h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hf))
      (J.smul_mem _ (h2 hm))
  have hS := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.submodule_generator_count O M ℓ e A J hx
  let f : (A ⧸ J.comap A.subtype) →ₗ[O] M ⧸ J := (J.comap A.subtype).mapQ J A.subtype le_rfl
  let g : (M ⧸ J) →ₗ[O] M ⧸ (A ⊔ J) :=
    J.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_right hx)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm
      obtain ⟨a, ha, j, hj, rfl⟩ := Submodule.mem_sup.1 hm
      refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype]
      rw [Submodule.Quotient.eq]
      simpa using J.neg_mem hj
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype, Submodule.Quotient.eq] at hx
      have e1 : m = (a : M) - ((a : M) - m) := by abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left a.2) (Submodule.mem_sup_right hx)
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hq : Module.length O (M ⧸ (A ⊔ J)) ≤ Module.length O (M ⧸ A) := by
    refine Module.length_le_of_surjective (A.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_left hx)) ?_
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  rw [hlen, add_comm]
  exact add_le_add hq hS

end Formalism.TruncatedSeriesCounting.R9
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.QNumericalIdentity
section
namespace Formalism.TruncatedSeriesCounting.X

theorem q_numerical_identity : QaNum := by
  intro ℓ hℓ H' H eW hH heW
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hdiv : ((H' / (ℓ - 1) : ℕ) : ℝ) ≤ (H' : ℝ) / ((ℓ : ℝ) - 1) := by
    have h := Nat.cast_div_le (m := H') (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h
  have hlog : Real.logb ℓ ((H' : ℝ) + 1) ≤ Real.logb ℓ (2 * (H : ℝ)) + 1 := by
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · subst h0
      have h0' : H' = 0 := by omega
      subst h0'
      simp
    · have h1 : (H' : ℝ) + 1 ≤ 2 * H := by
        have h2 : (H' : ℝ) ≤ H := by exact_mod_cast hH
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hpos
        linarith
      have h4 := Real.logb_le_logb_of_le hℓ1 (by positivity) h1
      linarith
  have hfrac : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤
      (H : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have heq : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
        (H' : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
      have := hd.ne'
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (pow_pos hd 2).le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by linarith)
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.X
end


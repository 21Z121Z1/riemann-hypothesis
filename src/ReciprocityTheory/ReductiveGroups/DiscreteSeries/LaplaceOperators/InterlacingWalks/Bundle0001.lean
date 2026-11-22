import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.AdjGap
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem adjGap_exists_change (f : ℕ → Bool) :
    ∀ d a : ℕ, f a ≠ f (a + d) → ∃ c, a ≤ c ∧ c < a + d ∧ f c ≠ f (c + 1) := by
  intro d
  induction d with
  | zero =>
    intro a h
    simp at h
  | succ d ih =>
    intro a h
    by_cases h1 : f a = f (a + d)
    · refine ⟨a + d, by omega, by omega, ?_⟩
      rw [← h1]
      simpa [Nat.add_assoc] using h
    · obtain ⟨c, h2, h3, h4⟩ := ih a h1
      exact ⟨c, h2, by omega, h4⟩

theorem adjGap_lt {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (hs : StrictAnti lam)
    (hadj : ∀ (a : Fin n) (ha : a.val + 1 < n), ε a ≠ ε ⟨a.val + 1, ha⟩ →
      h ≤ lam a - lam ⟨a.val + 1, ha⟩)
    (a b : Fin n) (hab : a.val < b.val) (hne : ε a ≠ ε b) : h ≤ lam a - lam b := by
  let f : ℕ → Bool := fun m => if hm : m < n then ε ⟨m, hm⟩ else false
  have hfa : ∀ x : Fin n, f x.val = ε x := fun x => by simp [f, x.2]
  obtain ⟨c, hc1, hc2, hc3⟩ := adjGap_exists_change f (b.val - a.val) a.val (by
    rw [show a.val + (b.val - a.val) = b.val by omega, hfa, hfa]
    exact hne)
  have hcn : c + 1 < n := by have := b.2; omega
  have hcn' : c < n := by omega
  have hne' : ε ⟨c, hcn'⟩ ≠ ε ⟨c + 1, hcn⟩ := by
    rw [← hfa ⟨c, hcn'⟩, ← hfa ⟨c + 1, hcn⟩]
    exact hc3
  have h1 : h ≤ lam ⟨c, hcn'⟩ - lam ⟨c + 1, hcn⟩ := hadj ⟨c, hcn'⟩ hcn hne'
  have h2 : lam ⟨c, hcn'⟩ ≤ lam a := hs.antitone (by rw [Fin.le_iff_val_le_val]; exact hc1)
  have h3 : lam b ≤ lam ⟨c + 1, hcn⟩ := hs.antitone (by rw [Fin.le_iff_val_le_val]; show c + 1 ≤ b.val; omega)
  linarith

theorem adjGap : AdjGapStatement := by
  unfold AdjGapStatement GapAtLeast
  intro n ε lam h hs hadj a b hab
  rcases lt_trichotomy a.val b.val with hlt | heq | hgt
  · exact le_trans (adjGap_lt ε lam h hs hadj a b hlt hab) (le_abs_self _)
  · exact absurd (congrArg ε (Fin.ext heq)) hab
  · rw [abs_sub_comm]
    exact le_trans (adjGap_lt ε lam h hs hadj b a hgt hab.symm) (le_abs_self _)

end ReciprocityTheory.ChartRestriction.DS.Lap
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Imports
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem seg : SegStatement := by
  intro n Q x s d N hx hstep
  have key : ∀ m : ℕ, m ≤ N → Q (x + ((m : ℝ) * d) • Pi.single s 1) := by
    intro m
    induction m with
    | zero => intro _; simpa using hx
    | succ m ih =>
      intro hm
      have h := hstep m (by omega) (ih (by omega))
      rw [Nat.cast_succ]
      exact h
  exact key N le_rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.WalkEnds
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem walkEnds : EndsStatement := by
  intro k r u v b t
  refine ⟨?_, ?_, ?_⟩
  · funext a
    have ha := a.isLt
    simp only [lamT, raisePar]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
      | (have h0 : a.val - (k - 1) = 0 := by omega
         simp [h0])
  · funext a
    have ha := a.isLt
    simp only [raisePar, walkPar, parLam]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
  · funext a
    simp [walkPar]

end ReciprocityTheory.ChartRestriction.DS.Lap
end


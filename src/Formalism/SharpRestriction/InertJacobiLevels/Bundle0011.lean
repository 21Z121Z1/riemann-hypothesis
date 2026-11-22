import Formalism.SharpRestriction.InertJacobiLevels.AsmLed

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.AsmErr
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def errPrimes (D : D7) : Finset ℕ :=
  haveI := D.wordFin
  ({D.host.g 0, D.host.g 1, D.host.d} : Finset ℕ) ∪ Finset.univ.image (fun u : D.what₂.Word => (D.mem u).A.T) ∪
    Finset.univ.biUnion (fun u : D.what₂.Word => (D.mem u).C.DGam.primeFactors)

open Classical in

def errSupp (D : D7) (sc : Scale) : Finset D.what₂.places.Pl :=
  (finite_resChar_le D (sc.X'' D.R.n)).toFinset ∪ (finite_resChar_mem D (errPrimes D)).toFinset

theorem Eval_off {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hw : w ∉ errSupp D L.sc) : Eval L X K c u j w = 0 := by
  classical
  let _ := D.wordFin
  rw [errSupp, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hw
  have h1 : ¬ ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n := hw.1
  have h2 : D.what₂.places.resChar w ∉ errPrimes D := hw.2
  refine Eval_above L X K c u j w (not_le.1 h1) ?_ ?_ ?_ ?_
  · intro h
    exact h2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨u, Finset.mem_univ _, h.symm⟩)))
  · intro h
    refine h2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h <;> simp [h]
  · intro h
    refine h2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    simp [h]
  · intro h
    refine h2 (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _, ?_⟩))
    exact Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, (D.mem u).C.DGam_pos.ne'⟩

variable {D : D7} {sc : Scale} {aT bT : D.host.TT → ℤ} {η Cc Ct CGam : ℝ} {j0 : ℕ}

def baseZ (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : SizeData₂ D :=
  baseL h Nu ∅ (fun _ _ _ => 0) (fun _ _ _ _ => rfl)

open Classical in

def baseE (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) : SizeData₂ D :=
  baseL h Nu (errSupp D sc ∪ S1) (Eval (baseZ h Nu) X K c)
    (fun u j w hw => Eval_off (baseZ h Nu) X K c u j w (fun h' => hw (Finset.mem_union_left _ h')))

open Classical in

theorem subset_supp_baseE (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) : S1 ⊆ (baseE h Nu S1 X K c).supp :=
  fun _ hw => Finset.mem_union_right _ hw

theorem edef_of_keeps (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) (L : SizeData₂ D) (h1 : L.sc = (baseE h Nu S1 X K c).sc)
    (h2 : L.etaSz = (baseE h Nu S1 X K c).etaSz) (h3 : L.Sc = (baseE h Nu S1 X K c).Sc)
    (h4 : L.E = (baseE h Nu S1 X K c).E) : L.EDef X K c := by
  intro u j _ w
  rw [h4]
  show Eval (baseZ h Nu) X K c u j w = Eval L X K c u j w
  unfold Eval EatG EatC EatI EatX
  rw [h1, h2, h3]
  rfl

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.SecondTorsionCardPos
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def ej (R : Ranks) (p : HCParam R) (j : ℕ) : ℝ := if h : j - 1 < R.m then ((p.e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

theorem wj_ej (D : D7) (j : ℕ) (τ : D.what₂.Tau) : wj D j τ = ej D.R (D.hc τ) j := rfl

theorem forall_tau (D : D7) {Φ : ↥(D.R.Psi) → HCParam D.R → Prop} (h : ∀ g, Φ g ((coreOf D).2.2 g))
    (τ : D.what₂.Tau) : Φ (D.eTau τ) (D.hc τ) := by
  have h1 := h (D.eTau τ)
  have e : (coreOf D).2.2 (D.eTau τ) = D.hc τ := congrArg D.hc (D.eTau.symm_apply_apply τ)
  rwa [e] at h1

structure CoreLed (R : Ranks) (H : Host R) (hc : ↥(R.Psi) → HCParam R) (sc : Scale) (a b : ℕ → ℤ)
    (η Cc Ct : ℝ) (j0 : ℕ) (Del : ℝ) : Prop where
  aT_win : ∀ t ∈ H.TT, sc.a ≤ (a t.val : ℝ) ∧ (a t.val : ℝ) ≤ sc.a + sc.a / ((R.k : ℝ) * sc.x ^ (Scale.A / 2))
  bT_ge : ∀ t ∈ H.TT, sc.b' ≤ (b t.val : ℝ)
  top_u : ∀ g : ↥(R.Psi), ∀ t ∈ H.TT, ∀ h0 : 0 < R.k, (g : R.GG) = R.tau1 t →
    (((hc g).u ⟨0, h0⟩ : ℚ) : ℝ) = a t.val + ((R.k : ℝ) - 1) / 2 ∧
    (((hc g).u ⟨R.k - 1, by omega⟩ : ℚ) : ℝ) = -(b t.val : ℝ) - ((R.k : ℝ) - 1) / 2
  top_b : ∀ g : ↥(R.Psi), ∀ t ∈ H.TT, ∀ hm : 0 < R.m, (g : R.GG) = R.tau1 t →
    (((hc g).b ⟨0, hm⟩ : ℚ) : ℝ) - (b t.val : ℝ) > ((R.k : ℝ) - 1) / 2 + 3
  b_le : ∀ g j, (((hc g).b j : ℚ) : ℝ) ≤ sc.b ^ 2
  logFiveDepth_le : Real.logb 5 ((R.n : ℝ) * R.N R.m / R.m) ≤ j0
  weightLength_ge_depth : 10 * j0 + 20 ≤ H.Lw
  split_tie : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ H.splitBound
  secondTorsion_card_pos : 0 < H.T2.card
  secondTorsion_card_le : H.T2.card ≤ R.n
  win_thick : ∀ j, 1 ≤ j → j ≤ R.m → ∀ g : ↥(R.Psi), (g : R.GG) ∈ H.thickPlaces →
    sc.b ≤ ej R (hc g) j ∧ ej R (hc g) j ≤ sc.b + η + 1
  win_top : ∀ j, 1 ≤ j → j ≤ R.m → ∀ g : ↥(R.Psi), ∀ t ∈ H.TT, (g : R.GG) = R.tau1 t →
    (b t.val : ℝ) + sc.b' / sc.x ≤ ej R (hc g) j ∧ ej R (hc g) j ≤ (b t.val : ℝ) + sc.b' / sc.x + η
  win_thin : ∀ j, 1 ≤ j → j ≤ R.m → ∀ g : ↥(R.Psi), H.IsThin (g : R.GG) →
    sc.w'' R.n ≤ ej R (hc g) j ∧ ej R (hc g) j ≤ sc.w'' R.n + η
  cloud_gap : ∀ (g : ↥(R.Psi)) (h0 : 0 < R.k - 1), (g : R.GG) ∉ H.topPlaces →
    (R.k : ℝ) * (4 * Del) ≤ (((hc g).u ⟨0, by omega⟩ - (hc g).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
    (((hc g).u ⟨0, by omega⟩ - (hc g).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((R.k : ℝ) * (4 * Del))
  cloud_v : ∀ g (i : Fin (R.k - 1)), 0 ≤ (((hc g).v i : ℚ) : ℝ) ∧ (((hc g).v i : ℚ) : ℝ) ≤ (R.k : ℝ) * (4 * Del)
  cloud_u : ∀ g (i : Fin R.k), 1 ≤ i.1 → i.1 + 1 < R.k →
    0 ≤ (((hc g).u i : ℚ) : ℝ) ∧ (((hc g).u i : ℚ) : ℝ) ≤ (R.k : ℝ) * (4 * Del)
  be_close : ∀ g (i j : Fin R.m), |(((hc g).b i - (hc g).e j : ℚ) : ℝ)| ≤ η
  eta_pos : 0 < η
  Del_pos : 0 < Del
  t_win : 1 ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ sc.x ^ Ct

def Core.Led (X : Core) (sc : Scale) (a b : ℕ → ℤ) (η Cc Ct : ℝ) (j0 : ℕ) (Del : ℝ) : Prop :=
  CoreLed X.1 X.2.1 X.2.2 sc a b η Cc Ct j0 Del

end Formalism.MainNotions.Inhab

end
end


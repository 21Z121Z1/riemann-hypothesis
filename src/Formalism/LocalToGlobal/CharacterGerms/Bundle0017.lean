import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
import Formalism.LocalToGlobal.CharacterGerms.Bundle0012

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NormOneRowDegrees
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

namespace WeightHomogeneousMinors

section WH

variable {R : Type} [CommRing R]

theorem isWH_rename {σ τ : Type} {w : τ → ℕ} (f : σ → τ) {p : MvPolynomial σ R} {D : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) p D) : IsWeightedHomogeneous w (rename f p) D := by
  intro dd hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero f p dd hd
  rw [← h hu, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rfl

theorem isWH_of_zero {σ : Type} {w : σ → ℕ} (hw : ∀ x, w x = 0) (p : MvPolynomial σ R) :
    IsWeightedHomogeneous w p 0 := by
  intro dd _
  simp [Finsupp.weight_apply, hw]

theorem isWH_congr {σ : Type} {w w' : σ → ℕ} (h : ∀ x, w x = w' x) {p : MvPolynomial σ R} {D : ℕ}
    (hp : IsWeightedHomogeneous w' p D) : IsWeightedHomogeneous w p D := by
  obtain rfl : w = w' := funext h
  exact hp

theorem isWH_deg {σ : Type} {w : σ → ℕ} {p : MvPolynomial σ R} {D D' : ℕ}
    (hp : IsWeightedHomogeneous w p D) (e : D = D') : IsWeightedHomogeneous w p D' := by
  subst e; exact hp

theorem isWH_minorK_gen {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (v : Fin N' → ℕ) (hw : ∀ x, w x = v x.2)
    (h : k ≤ N ∧ k ≤ N') :
    IsWeightedHomogeneous w (minorK R N N' k) (∑ c : Fin k, v (Fin.castLE h.2 c)) := by
  unfold minorK
  rw [dif_pos h, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : IsWeightedHomogeneous w (∏ i : Fin k, (Matrix.of fun b c : Fin k =>
      (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') R)) (σ i) i)
      (∑ c : Fin k, v (Fin.castLE h.2 c)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      simp only [Matrix.of_apply]
      have hx := isWeightedHomogeneous_X R w (Fin.castLE h.1 (σ i), Fin.castLE h.2 i)
      rwa [hw] at hx
  intro dd hdd
  apply hprod
  intro h0
  apply hdd
  rw [MvPolynomial.coeff_smul, h0, smul_zero]

theorem sum_fin_ite (k c0 : ℕ) : (∑ c : Fin k, if (c : ℕ) = c0 then 1 else 0) = if c0 < k then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c0, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro hc; exact hb (Fin.ext hc)
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro hc
    exact h (by rw [← hc]; exact c.2)

theorem isWH_minorK_row {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (P : Prop) [Decidable P] (c0 : ℕ)
    (hw : ∀ x, w x = if P ∧ (x.2 : ℕ) = c0 then 1 else 0) :
    IsWeightedHomogeneous w (minorK R N N' k) (if k ≤ N ∧ k ≤ N' ∧ P ∧ c0 < k then 1 else 0) := by
  by_cases h : k ≤ N ∧ k ≤ N'
  · have hg := isWH_minorK_gen (R := R) (fun c : Fin N' => if P ∧ (c : ℕ) = c0 then 1 else 0) hw h
    refine isWH_deg hg ?_
    by_cases hP : P
    · simp only [hP, true_and, Fin.coe_castLE]
      rw [sum_fin_ite]
      simp [h.1, h.2, hP]
    · simp [hP]
  · unfold minorK
    rw [dif_neg h, if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
    exact isWeightedHomogeneous_one R w

end WH

section Let

variable {T : Type} (r : T → ℕ) (n : ℕ)

def wLet (σ : T) (c0 : Fin (r σ)) (ℓ : Letter T r n) : ℕ := ∑ b : Fin n, if ℓ = ⟨σ, c0, b⟩ then 1 else 0

theorem weight_wLet (σ : T) (c0 : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (wLet r n σ c0) m = ∑ b : Fin n, m ⟨σ, c0, b⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [wLet, smul_eq_mul, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    exact h.symm

variable {r n}

theorem letEq {τ1 τ2 : T} {c1 : Fin (r τ1)} {c2 : Fin (r τ2)} {b1 b2 : Fin n} :
    ((⟨τ1, (c1, b1)⟩ : Letter T r n) = ⟨τ2, (c2, b2)⟩) ↔ ((⟨τ1, c1⟩ : Σ σ, Fin (r σ)) = ⟨τ2, c2⟩ ∧ b1 = b2) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, rfl⟩
    cases h1
    rfl

theorem wLet_mk (σ : T) (c0 : Fin (r σ)) (τ : T) (c : Fin (r τ)) (ρ : Fin n) :
    wLet r n σ c0 ⟨τ, (c, ρ)⟩ = if (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0 := by
  unfold wLet
  simp only [letEq]
  by_cases h : (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩
  · simp only [h, true_and, if_true]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

end Let

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]

def wRow (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o0 : Orb) {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ)
    (x : Fin N × WV (IIof r tau o0)) : ℕ :=
  if x.2.1 = g0 ∧ x.2.2.1 = t0 ∧ (x.2.2.2 : ℕ) = c0 then 1 else 0

variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)

include hty in
theorem en_fst (g : Fin 2) (t : ZMod d) (c : Fin (X.rkF g t)) : (F.en g t c).1 = t := by
  rw [← hty g (F.en g t c)]
  exact F.en_ty g t c

include hty in
theorem rkF_eq (g : Fin 2) (t : ZMod d) : X.rkF g t = r (tau o0 g t) := by
  unfold RowData.rkF
  have hc : (Finset.univ : Finset (Fin (r (tau o0 g t)))).card = r (tau o0 g t) := by simp
  rw [← hc]
  symm
  apply Finset.card_bij (fun c _ => (⟨t, c⟩ : IIof r tau o0 g))
  · intro c _; simp [hty]
  · intro c1 _ c2 _ h; simpa using h
  · rintro ⟨t', c⟩ hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hty] at hc'
    subst hc'
    exact ⟨c, Finset.mem_univ _, rfl⟩

include hty std in
theorem wRow_letter {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d)
    (x : Fin N × Fin (X.rkF g t)) :
    wRow r tau o0 g0 t0 c0 (F.letter g t x) = if (g = g0 ∧ t = t0) ∧ (x.2 : ℕ) = c0 then 1 else 0 := by
  unfold wRow Flag.letter
  simp only [en_fst X F hty, std]
  simp only [and_assoc]

include hty std in
theorem isWH_letter_minorK {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRow r tau o0 (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) := by
  apply isWH_rename
  exact isWH_minorK_row (R := C) (g = g0 ∧ t = t0) c0 (fun x => wRow_letter X F hty std g0 t0 c0 g t x)

include hty in
theorem num_ch (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (r (tau o0 g0 t0)), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g0 = g ∧ t0 = t
  · obtain ⟨rfl, rfl⟩ := hg
    rw [rkF_eq X hty]
    simp only [le_refl, true_and, eq_self_iff_true]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_Icc]
    by_cases hc : X.n ≤ r (tau o0 g0 t0) ∧ c0 < X.n
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩, smul_eq_mul, mul_one]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.2, by omega⟩), smul_zero]
  · rw [Finset.sum_eq_zero (fun k _ => if_neg (fun h => hg ⟨h.1, h.2.1⟩))]
    rw [if_neg (fun h => hg ⟨h.2.2.1.1.symm, h.2.2.1.2.symm⟩), smul_zero]

include hty in
theorem num_mon (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (r (tau o0 g0 t0)),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g = g0
  · subst hg
    rw [Finset.sum_eq_single t0]
    · rw [rkF_eq X hty]
      have hL : ∀ k ∈ Finset.Icc 1 (min N (r (tau o0 g t0))),
          e t0 k • (if k ≤ N ∧ k ≤ r (tau o0 g t0) ∧ (g = g ∧ t0 = t0) ∧ c0 < k then 1 else 0) =
            if c0 < k then e t0 k else 0 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        by_cases hc : c0 < k
        · rw [if_pos ⟨by omega, by omega, ⟨rfl, rfl⟩, hc⟩, if_pos hc, smul_eq_mul, mul_one]
        · rw [if_neg (fun h => hc h.2.2.2), if_neg hc, smul_zero]
      rw [Finset.sum_congr rfl hL, ← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, eq_self_iff_true, true_and]
      omega
    · intro t _ ht
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
    · simp
  · trans 0
    · exact Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun k _ => by
        rw [if_neg (fun h => hg h.2.2.1.1), smul_zero]
    · exact (Finset.sum_eq_zero fun k _ => if_neg (fun h => hg h.1.symm)).symm

end Block

end WeightHomogeneousMinors

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

def keyL (ℓ : Letter T r n) : T × ℕ × Fin n := (ℓ.1, ℓ.2.1.val, ℓ.2.2)

theorem keyL_inj : Function.Injective (keyL (T := T) (r := r) (n := n)) := by
  rintro ⟨σ, i, c⟩ ⟨σ', i', c'⟩ h
  simp only [keyL, Prod.mk.injEq] at h
  obtain ⟨rfl, hi, rfl⟩ := h
  obtain rfl : i = i' := Fin.ext hi
  rfl

theorem rowShift_X (σ : T) (i i' : Fin (r σ)) (t : C) (ℓ : Letter T r n) :
    rowShift r n C σ i i' t (X ℓ) =
      if keyL ℓ = (σ, i.val, ℓ.2.2) then X ℓ + MvPolynomial.C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ := by
  unfold rowShift
  simp only [MvPolynomial.aeval_X]
  have key : (∃ b, ℓ = ⟨σ, (i, b)⟩) ↔ keyL ℓ = (σ, ↑i, ℓ.snd.2) := by
    constructor
    · rintro ⟨b, rfl⟩
      rfl
    · intro h
      exact ⟨ℓ.snd.2, keyL_inj (show keyL ℓ = keyL ⟨σ, (i, ℓ.snd.2)⟩ from h)⟩
  by_cases h : keyL ℓ = (σ, ↑i, ℓ.snd.2)
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (mt key.mp h), if_neg h]

private theorem det_mapMatrix_shear_eq_det {K : ℕ} (A : Matrix (Fin K) (Fin K) (MvPolynomial (Letter T r n) C))
    (μ : Fin K → Fin K → Letter T r n) (hA : ∀ b c, A b c = X (μ b c)) (σ0 : T) (κ : Fin K → Fin n)
    (hμ : ∀ b c, keyL (μ b c) = (σ0, c.val, κ b)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    ((rowShift r n C σ i i' t).mapMatrix A).det = A.det := by
  have h3 : ∀ b c, (μ b c).snd.2 = κ b := fun b c => congrArg (fun p => p.2.2) (hμ b c)
  by_cases hc : σ = σ0 ∧ i.val < K
  · obtain ⟨hσ, hiK⟩ := hc
    subst σ0
    have hi'K : i'.val < K := lt_trans hi hiK
    let c0 : Fin K := ⟨i.val, hiK⟩
    let c1 : Fin K := ⟨i'.val, hi'K⟩
    have hne : c0 ≠ c1 := by
      intro h
      have h' := congrArg Fin.val h
      exact hi.ne' (Fin.ext h')
    have h1 : ∀ b, μ b c1 = ⟨σ, (i', κ b)⟩ := fun b =>
      keyL_inj (show keyL (μ b c1) = keyL ⟨σ, (i', κ b)⟩ from hμ b c1)
    have hmat : (rowShift r n C σ i i' t).mapMatrix A =
        A.updateCol c0 (fun b => A b c0 + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b c1) := by
      ext b c
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply, hA, rowShift_X, hμ, h3, h1]
      by_cases hcc : c = c0
      · have hv : (c : ℕ) = i.val := by rw [hcc]
        rw [if_pos (by rw [hv]), if_pos hcc, hcc, smul_eq_mul]
      · have hv : (c : ℕ) ≠ i.val := fun h => hcc (Fin.ext h)
        rw [if_neg (by simp [hv]), if_neg hcc]
    rw [hmat]
    exact Matrix.det_updateCol_add_smul_self A hne (MvPolynomial.C t : MvPolynomial (Letter T r n) C)
  · congr 1
    ext b c
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, hA, rowShift_X, hμ, h3]
    rw [if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hc ⟨h.1.symm, by rw [← h.2.1]; exact c.isLt⟩

theorem rowShift_minor {N N' : ℕ} (lam : Fin N × Fin N' → Letter T r n) (σ0 : T) (col : Fin N → Fin n)
    (hlam : ∀ ρ c, keyL (lam (ρ, c)) = (σ0, c.val, col ρ)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (rename lam (minorK C N N' k)) = rename lam (minorK C N N' k) := by
  unfold minorK
  split_ifs with hk
  · rw [AlgHom.map_det, AlgHom.map_det]
    exact det_mapMatrix_shear_eq_det _ (fun b c => lam (Fin.castLE hk.1 b, Fin.castLE hk.2 c))
      (fun b c => by simp [rename_X]) σ0 (fun b => col (Fin.castLE hk.1 b))
      (fun b c => hlam (Fin.castLE hk.1 b) (Fin.castLE hk.2 c)) σ i i' hi t
  · simp

theorem rowShift_monP {N N' : ℕ} (lam : Fin N × Fin N' → Letter T r n) (σ0 : T) (col : Fin N → Fin n)
    (hlam : ∀ ρ c, keyL (lam (ρ, c)) = (σ0, c.val, col ρ)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (e : ℕ → ℕ) :
    rowShift r n C σ i i' t (rename lam (monP C N N' e)) = rename lam (monP C N N' e) := by
  unfold monP
  simp only [map_prod, map_pow, rowShift_minor lam σ0 col hlam σ i i' hi t]

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}

def psiL (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (n : ℕ) (o : Orb) {N : ℕ} (col : Fin N → Fin n)
    (x : Fin N × WV (IIof r tau o)) : Letter T r n := phiL r tau n (col x.1, ⟨o, x.2⟩)

theorem ConjugatePairPlaceSetting.key_letter (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (t : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (ρ : Fin N) (q : Fin ((X o).rkF g t)) :
    keyL ((psiL r tau n o col ∘ (F o).letter g t) (ρ, q)) = (tau o g t, q.val, col ρ) := by
  simp only [Function.comp_apply, psiL, Flag.letter, phiL, keyL]
  have h1 : ((F o).en g t q).fst = t := by
    have h := (F o).3 g t q
    rw [H.hty] at h
    exact h
  rw [H.std o g t q, h1]

theorem ConjugatePairPlaceSetting.inv_minor (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k))) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k)) := by
  rw [rename_rename]
  exact rowShift_minor _ (tau o g s) col (fun ρ c => H.key_letter o g s col ρ c) σ i i' hi t k

theorem ConjugatePairPlaceSetting.inv_mon (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (e : ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (rename ((F o).letter g s) (monP C N ((X o).rkF g s) e))) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (monP C N ((X o).rkF g s) e)) := by
  rw [rename_rename]
  exact rowShift_monP _ (tau o g s) col (fun ρ c => H.key_letter o g s col ρ c) σ i i' hi t e

theorem ConjugatePairPlaceSetting.inv_bi (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C N ((X o).rkF g' s') k) ^ e2)) =
      rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C N ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_pow, map_mul, H.inv_minor o g s col k σ i i' hi t, H.inv_minor o g' s' col k σ i i' hi t]

theorem ConjugatePairPlaceSetting.inv_ch (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k e1 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1)) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1) := by
  simp only [map_pow, H.inv_minor o g s col k σ i i' hi t]

theorem ConjugatePairPlaceSetting.inv_monAll (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) {N : ℕ}
    (col : Fin N → Fin n) (e : ZMod d → ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (∏ s : ZMod d, rename ((F o).letter g s) (monP C N ((X o).rkF g s) (e s)))) =
      rename (psiL r tau n o col) (∏ s : ZMod d, rename ((F o).letter g s) (monP C N ((X o).rkF g s) (e s))) := by
  simp only [map_prod]
  exact Finset.prod_congr rfl fun s _ => H.inv_mon o g s col (e s) σ i i' hi t

theorem ConjugatePairPlaceSetting.inv_poly (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (b : GlobalTheory d) (col : Fin (b.what₂ (X o).n) → Fin n)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (b.poly (X o) (F o))) =
      rename (psiL r tau n o col) (b.poly (X o) (F o)) := by
  rcases b with ⟨g, a, j, y⟩ | ⟨g, a, u⟩ | ⟨g, e, N⟩
  · exact H.inv_bi o _ _ _ _ col _ _ _ σ i i' hi t
  · exact H.inv_ch o _ _ col _ _ σ i i' hi t
  · exact H.inv_monAll o _ col _ σ i i' hi t

end Fam

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePGaugeMapSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ}

private theorem cc_subst_lemma_2 {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem cc_ev_eq {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma_2 (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem constantCoeff_eval_pair {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    constantCoeff (ev ![a, b] f) = constantCoeff f := cc_ev_eq ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MapFB

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePNvalEqSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem nvalEqSt_holds : NvalEqSt := by
  intro T C _ V ι hι x
  unfold nval eOf
  have hl : 0 ≤ vV T.V ((V.l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rwa [map_natCast] at h
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl, map_zero, AddValuation.map_zero]
    rfl
  · rw [if_neg hx, hι x hx]
    have he : ((vV T.V ((V.l : ℕ) : T.Fr)).toNat : ℝ) = (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
      first
        | exact_mod_cast Int.toNat_of_nonneg hl
        | rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg hl]
    rw [he]
    rfl

end Formalism.L2.FormalSeriesBounds
end
end


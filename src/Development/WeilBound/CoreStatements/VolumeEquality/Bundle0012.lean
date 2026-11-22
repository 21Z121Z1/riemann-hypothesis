import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestA
section
noncomputable section

namespace SheetDecomposition

open MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

section Relabel

variable {Ψ Ψ' : Type} [Fintype Ψ] [DecidableEq Ψ] [Fintype Ψ'] [DecidableEq Ψ'] {N : ℕ} (e : Ψ ≃ Ψ')

theorem degFl_rename (F : RP Ψ N) : degFl (rename (e.prodCongr (Equiv.refl (Fin N))) F : RP Ψ' N) = degFl F := by
  unfold degFl
  have hd : dimFl Ψ' N = dimFl Ψ N := by
    unfold dimFl
    rw [Fintype.card_congr e]
  rw [hd, ← (Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))).sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp : permExp ((Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))) σ) =
      Finsupp.mapDomain (e.prodCongr (Equiv.refl (Fin N))) (permExp σ) := by
    ext ⟨τ', i⟩
    rw [Finsupp.mapDomain_equiv_apply]
    simp [permExp]
  rw [hp, coeff_rename_mapDomain _ (e.prodCongr (Equiv.refl (Fin N))).injective]
  congr 1
  exact Equiv.prod_comp e.symm (fun τ => ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ))

theorem rename_muSmall (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (muSmall j : RP Ψ N) : RP Ψ' N) = muSmall j := by
  unfold muSmall
  split_ifs
  · simp only [map_sum, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · simp only [pkLow, map_neg, map_sum, map_pow, rename_X, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem rename_fibClass (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (fibClass j : RP Ψ N) : RP Ψ' N) = fibClass j := by
  unfold fibClass
  simp only [map_prod, map_sub, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Relabel

theorem testRelabel : TestRelabel := by
  intro Ψ _ _ N j
  unfold testDeg
  rw [← degFl_rename (Fintype.equivFin Ψ), map_mul, map_pow, rename_muSmall, rename_fibClass]
  simp [dimX]

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {p q : ℕ}

theorem count_pairs : Fintype.card Ψ * p * q + Fintype.card (PairIx Ψ p q) = dimFl Ψ (p + q) := by
  classical
  have hL : (Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).card =
      (p + q) * (p + q - 1) / 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_range_id,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have hC : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
      fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)).card = p * q := by
    have e : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
        fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)) =
        (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p) ×ˢ
          (Finset.univ.filter fun b : Fin (p + q) => ¬ (b : ℕ) < p) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Fin.lt_iff_val_lt_val]
      omega
    have h1 : (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p).card = p := by
      rw [Fin.card_filter_val_lt]
      omega
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (p + q))))
      (fun a : Fin (p + q) => (a : ℕ) < p)
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    rw [e, Finset.card_product, h1]
    congr 1
    omega
  have hS : Fintype.card {ab : Fin (p + q) × Fin (p + q) // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)} +
      p * q = (p + q) * (p + q - 1) / 2 := by
    rw [Fintype.card_subtype, ← hL, ← hC, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [Fintype.card_prod]
  unfold dimFl
  rw [← hS]
  ring

def muCoef (Ψ : Type) (p q : ℕ) : Ψ × Fin (p + q) → ℤ := fun x => if p ≤ (x.2 : ℕ) then 1 else 0

def fibCoef (t : PairIx Ψ p q) : Ψ × Fin (p + q) → ℤ := fun x =>
  (if x = (t.1, t.2.1.2) then 1 else 0) - if x = (t.1, t.2.1.1) then 1 else 0

theorem sum_muCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) :
    ∑ r, muCoef Ψ p q r • x r = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q) => p ≤ (i : ℕ)), x (τ, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [muCoef]
  split_ifs <;> simp

theorem sum_fibCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) (t : PairIx Ψ p q) :
    ∑ r, fibCoef t r • x r = x (t.1, t.2.1.2) - x (t.1, t.2.1.1) := by
  simp [fibCoef, sub_smul, Finset.sum_sub_distrib, ite_smul]

theorem test_factor {n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (muSmall p ^ dimX Ψ (p + q) p * fibClass p : RP Ψ (p + q)) =
      ∏ j : Fin (n + r), ∑ x, Fin.append (fun _ : Fin n => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have hN : p + q - p ≤ p := by omega
  have hmu : (muSmall p : RP Ψ (p + q)) = ∑ x, muCoef Ψ p q x • (X x : RP Ψ (p + q)) := by
    rw [sum_muCoef (X : Ψ × Fin (p + q) → RP Ψ (p + q))]
    unfold muSmall
    rw [if_pos hN]
  have hdim : dimX Ψ (p + q) p = n := by
    unfold dimX
    rw [hn, Nat.add_sub_cancel_left]
    ring
  have hfib : (fibClass p : RP Ψ (p + q)) = ∏ i : Fin r, ∑ x, fibCoef (e i) x • (X x : RP Ψ (p + q)) := by
    simp only [sum_fibCoef]
    rw [Fintype.prod_equiv e _ (fun t : PairIx Ψ p q => (X (t.1, t.2.1.2) - X (t.1, t.2.1.1) : RP Ψ (p + q)))
      (fun _ => rfl)]
    unfold fibClass
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
    try rfl
  rw [Fin.prod_univ_add, hmu, hdim, hfib]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushVal
section
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {K'' : Type} [Fintype K''] {ι'' : K'' → Type}
  [∀ b, Fintype (ι'' b)]

theorem vsup_ne_zero (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} {b : K} (h : ∃ i, y ⟨b, i⟩ ≠ 0) :
    (Finset.univ.sup fun i => O.valuation (y ⟨b, i⟩)) ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  have h1 : O.valuation (y ⟨b, i⟩) ≤ Finset.univ.sup fun i => O.valuation (y ⟨b, i⟩) :=
    Finset.le_sup (f := fun i => O.valuation (y ⟨b, i⟩)) (Finset.mem_univ i)
  rw [h0] at h1
  exact hi ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))

theorem vdeg_ne_zero (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (a : K → ℤ) :
    vdeg O y a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (vsup_ne_zero O (h b))

@[simp] theorem vdeg_zero (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) : vdeg O y 0 = 1 := by simp [vdeg]

theorem vdeg_add (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (a a' : K → ℤ) :
    vdeg O y (a + a') = vdeg O y a * vdeg O y a' := by
  unfold vdeg
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun b _ => zpow_add₀ (vsup_ne_zero O (h b)) _ _

theorem vdeg_neg (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (a : K → ℤ) : vdeg O y (-a) = (vdeg O y a)⁻¹ := by
  unfold vdeg
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun b _ => zpow_neg _ _

theorem vdeg_sub (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (a a' : K → ℤ) :
    vdeg O y (a - a') = vdeg O y a / vdeg O y a' := by
  rw [sub_eq_add_neg, vdeg_add O h, vdeg_neg, div_eq_mul_inv]

theorem vdeg_sum (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) {T : Type} (s : Finset T)
    (a : T → K → ℤ) : vdeg O y (∑ t ∈ s, a t) = ∏ t ∈ s, vdeg O y (a t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s ht ih => rw [Finset.sum_insert ht, Finset.prod_insert ht, vdeg_add O h, ih]

theorem vdeg_join (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a a') = vdeg O y a * vdeg O y' a' := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  rfl

theorem vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a 0) = vdeg O y a := by rw [vdeg_join, vdeg_zero, mul_one]

theorem vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim 0 a') = vdeg O y' a' := by rw [vdeg_join, vdeg_zero, one_mul]

theorem joinPt_ne {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) :
    ∀ b, ∃ i, joinPt y y' ⟨b, i⟩ ≠ 0
  | .inl b => h b
  | .inr b => h' b

namespace ValEq

variable {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {y'' : (Σ b, ι'' b) → Ω}

theorem of_eq {a : K → ℤ} {a' : K' → ℤ} (h : ∀ O : ValuationSubring Ω, vdeg O y a = vdeg O y' a') : ValEq k y a y' a' :=
  ⟨1, one_ne_zero, fun O _ => by rw [h O, map_one, one_mul]⟩

theorem refl (y : (Σ b, ι b) → Ω) (a : K → ℤ) : ValEq k y a y a := of_eq fun _ => rfl

theorem zero (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : ValEq k y 0 y' 0 := of_eq fun _ => by simp

theorem symm {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y' a' y a := by
  obtain ⟨ρ, h0, h⟩ := h
  refine ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => ?_⟩
  rw [h O hO, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]

theorem trans {a : K → ℤ} {a' : K' → ℤ} {a'' : K'' → ℤ} (h : ValEq k y a y' a') (h' : ValEq k y' a' y'' a'') :
    ValEq k y a y'' a'' := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  exact ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => by rw [h O hO, h' O hO, map_mul, mul_assoc]⟩

theorem add (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {a b : K → ℤ} {a' b' : K' → ℤ}
    (h : ValEq k y a y' a') (h' : ValEq k y b y' b') : ValEq k y (a + b) y' (a' + b') := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  refine ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => ?_⟩
  rw [vdeg_add O hy, vdeg_add O hy', h O hO, h' O hO, map_mul, mul_mul_mul_comm]

theorem neg {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y (-a) y' (-a') := by
  obtain ⟨ρ, h0, h⟩ := h
  exact ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => by rw [vdeg_neg, vdeg_neg, h O hO, map_inv₀, mul_inv]⟩

theorem sub (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {a b : K → ℤ} {a' b' : K' → ℤ}
    (h : ValEq k y a y' a') (h' : ValEq k y b y' b') : ValEq k y (a - b) y' (a' - b') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact add hy hy' h h'.neg

theorem sum (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {T : Type} (s : Finset T) {a : T → K → ℤ}
    {a' : T → K' → ℤ} (h : ∀ t ∈ s, ValEq k y (a t) y' (a' t)) : ValEq k y (∑ t ∈ s, a t) y' (∑ t ∈ s, a' t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero y y'
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht]
    exact add hy hy' (h t (Finset.mem_insert_self _ _)) (ih fun t' ht' => h t' (Finset.mem_insert_of_mem ht'))

theorem join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) : ValEq k (joinPt y y') (Sum.elim a 0) y a :=
  of_eq fun O => vdeg_join_inl O y y' a

theorem join_inr (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : ValEq k (joinPt y y') (Sum.elim 0 a') y' a' :=
  of_eq fun O => vdeg_join_inr O y y' a'

end ValEq

end SheetDecomposition
end
end


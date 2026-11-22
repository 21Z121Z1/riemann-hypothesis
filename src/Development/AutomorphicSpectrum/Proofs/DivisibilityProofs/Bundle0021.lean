import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SymmetricFormPolynomialCoeff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym

open MvPolynomial Finset

variable {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ}

def letterCount (w : Fin n → σ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (univ.filter fun r => w r = p).card

theorem letterCount_apply (w : Fin n → σ) (p : σ) :
    letterCount w p = (univ.filter fun r => w r = p).card := rfl

theorem prod_X_eq_monomial (w : Fin n → σ) :
    (∏ j, (X (w j) : MvPolynomial σ ℝ)) = monomial (letterCount w) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    ← Finset.prod_fiberwise univ w]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => (X p : MvPolynomial σ ℝ))
    (fun j hj => by rw [(Finset.mem_filter.1 hj).2])]
  simp [letterCount_apply]

theorem letterCount_comp (w : Fin n → σ) (π : Equiv.Perm (Fin n)) :
    letterCount (w ∘ π) = letterCount w := by
  ext p
  rw [letterCount_apply, letterCount_apply]
  exact Finset.card_equiv π (fun r => by simp)

theorem exists_perm_of_letterCount_eq (w w₀ : Fin n → σ) (h : letterCount w = letterCount w₀) :
    ∃ π : Equiv.Perm (Fin n), w₀ ∘ π = w := by
  have e : ∀ p, {r // w r = p} ≃ {r // w₀ r = p} := fun p => Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact DFunLike.congr_fun h p)
  exact ⟨Equiv.ofFiberEquiv e, funext fun r => Equiv.ofFiberEquiv_map e r⟩

theorem card_letterCount_mul (w₀ : Fin n → σ) :
    (univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card *
      ∏ p, (letterCount w₀ p).factorial = n.factorial := by
  have hst : Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} =
      ∏ p, (letterCount w₀ p).factorial := by
    rw [DomMulAct.stabilizer_card]
    exact Finset.prod_congr rfl fun p _ => by rw [Fintype.card_subtype, letterCount_apply]
  have hcard : (univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    simp [Finset.card_univ, Fintype.card_perm]
  have hfib : ∀ w ∈ univ.filter (fun w : Fin n → σ => letterCount w = letterCount w₀),
      (univ.filter fun π : Equiv.Perm (Fin n) => w₀ ∘ π = w).card =
        Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} := by
    intro w hw
    obtain ⟨π₀, rfl⟩ := exists_perm_of_letterCount_eq w w₀ (Finset.mem_filter.1 hw).2
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulRight π₀⁻¹) fun g => ?_)
    constructor
    · intro h
      funext r
      have := congrFun h (π₀⁻¹ r)
      simpa using this
    · intro h
      funext r
      have := congrFun h (π₀ r)
      simpa using this
  rw [← hst, ← hcard, Finset.card_eq_sum_card_fiberwise (s := univ)
    (f := fun π : Equiv.Perm (Fin n) => w₀ ∘ π)
    (t := univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀)
    (fun π _ => by simp [letterCount_comp]), Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

theorem coeff_formPoly_mul (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (hsym : ∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) (w₀ : Fin n → σ) (m : σ →₀ ℕ)
    (hm : ∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) :
    coeff m (PB.formPoly n a) * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ := by
  obtain rfl : m = letterCount w₀ := Finsupp.ext fun p => by rw [hm, letterCount_apply]
  have hc : coeff (letterCount w₀) (PB.formPoly n a) =
      ((univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card : ℝ) * a w₀ := by
    unfold PB.formPoly
    rw [coeff_sum, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [prod_X_eq_monomial, coeff_C_mul, coeff_monomial]
    by_cases h : letterCount w = letterCount w₀
    · obtain ⟨π, rfl⟩ := exists_perm_of_letterCount_eq w w₀ h
      simp [letterCount_comp, hsym]
    · simp [h]
  rw [hc, ← card_letterCount_mul w₀]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightGapDeltaEqAntisymmetric
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def xAt {Ψ : Type} {N : ℕ} (τ : Ψ) (i : ℕ) : MvPolynomial (Ψ × Fin N) ℝ :=
  if h : i < N then X (τ, ⟨i, h⟩) else 0

theorem xAt_val {Ψ : Type} {N : ℕ} (τ : Ψ) (a : Fin N) :
    (xAt τ (a : ℕ) : MvPolynomial (Ψ × Fin N) ℝ) = X (τ, a) := by
  simp [xAt]

theorem gapX_eq_xAt_sub {Ψ : Type} {N : ℕ} (τ : Ψ) (s : Fin N) :
    PB.gapX (τ, s) = xAt τ (s : ℕ) - xAt τ ((s : ℕ) + 1) := by
  simp [PB.gapX, xAt]

theorem sum_gapX_Ico {Ψ : Type} {N : ℕ} (τ : Ψ) {a b : Fin N} (hab : a ≤ b) :
    ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s) = X (τ, a) - X (τ, b) := by
  have h1 : ∑ s ∈ Finset.Ico a b, PB.gapX (τ, s)
      = ∑ i ∈ Finset.Ico (a : ℕ) (b : ℕ),
          ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1)) := by
    rw [← Fin.map_valEmbedding_Ico, Finset.sum_map]
    exact Finset.sum_congr rfl fun s _ => gapX_eq_xAt_sub τ s
  have hle : (a : ℕ) ≤ b := hab
  have h2 : ∀ n : ℕ, ∑ i ∈ Finset.Ico (a : ℕ) ((a : ℕ) + n),
      ((xAt τ i : MvPolynomial (Ψ × Fin N) ℝ) - xAt τ (i + 1))
        = xAt τ (a : ℕ) - xAt τ ((a : ℕ) + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right _ _), ih]
      ring
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hle
  rw [h1, hn, h2, ← hn, xAt_val, xAt_val]

theorem toWt_gapDelta_eq_antisymDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := by
  unfold gapDelta GroundTheory.Heights₂.Heights.antisymDelta
  simp only [map_prod, map_sum]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ =>
    Finset.prod_congr rfl fun b hb => ?_
  have hab : a ≤ b := (Finset.mem_Ioi.1 hb).le
  rw [← sum_gapX_Ico τ hab]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [PB.toWt]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightMapInjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem aeval_tail_gapX {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) :
    (aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)))
      (PB.gapX p) = X p := by
  obtain ⟨τ, i⟩ := p
  simp only [PB.gapX, map_sub, aeval_X]
  split_ifs with h
  · rw [aeval_X]
    have hI : Finset.Ici i = insert i (Finset.Ici (⟨(i : ℕ) + 1, h⟩ : Fin N)) := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    rw [hI, Finset.sum_insert (by simp [Fin.le_def])]
    ring
  · have hI : Finset.Ici i = {i} := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [map_zero, sub_zero, hI, Finset.sum_singleton]

theorem toWt_leftInverse_injective (Ψ : Type) (N : ℕ) :
    Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  set T : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)) with hT
  have hli : T.comp PB.toWt = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, AlgHom.id_apply, PB.toWt, aeval_X, hT]
    exact aeval_tail_gapX p
  intro a b hab
  have ha : T (PB.toWt a) = a := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  have hb : T (PB.toWt b) = b := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  rw [← ha, ← hb, hab]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end


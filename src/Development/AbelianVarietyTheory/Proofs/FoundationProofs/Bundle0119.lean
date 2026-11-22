import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelMassDegreeTypeLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompactStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_isOpen_isCompact | exact GlobalTheory.PsType.grp_isOpen_isCompact | (intros; apply GlobalTheory.PsType.grp_isOpen_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section

namespace GlobalTheory.PsType.BlockTheta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_mul_char (χ η : kˣ →* ℂˣ) (x : k) : ev (χ * η) x = ev χ x * ev η x := by
  unfold ev
  split_ifs with h
  · simp
  · simp

theorem ev_one_char (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

theorem ev_at_one (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  rw [dif_pos (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem ev_mul_of_val (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
  unfold ev
  rw [dif_pos hxy, dif_pos hx, dif_pos hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext; simp

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (h : Triv χ 1) (x : k) : ev χ x = 1 := by
  unfold ev
  split_ifs with hx
  · have hu : χ (Units.mk0 x fun h0 => by simp [h0] at hx) = 1 := by
      refine h _ (by simpa using hx) ?_
      calc valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) - 1 : k)
          ≤ max (valuation k x) (valuation k 1) := by rw [Units.val_mk0]; exact Valuation.map_sub _ _ _
        _ = valuation k 1 := by rw [hx, map_one, max_self]
    simp [hu]
  · rfl

theorem val_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have h1 : ((Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)) A).val.det
      = algebraMap 𝒪[k] k A.val.det := by
    simp [RingHom.map_det]
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Matrix.isUnits_det_units A)

def head {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) : kˣ →* ℂˣ := if h : 0 < n then ψ ⟨0, h⟩ else 1

theorem prod_ev_nxt : ∀ (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (x : k),
    ∏ m, ev (ψ m / nxt ψ m) x = ev (head ψ) x
  | 0, ψ, x => by simp [head, ev_one_char]
  | n + 1, ψ, x => by
    rw [Fin.prod_univ_succ]
    have h1 : ∀ j : Fin n, nxt ψ j.succ = nxt (fun i => ψ i.succ) j := by
      intro j; unfold nxt
      by_cases h : (j : ℕ) + 1 < n
      · rw [dif_pos (by simp [Fin.val_succ]; omega), dif_pos h]; congr 1
      · rw [dif_neg (by simp [Fin.val_succ]; omega), dif_neg h]
    have h2 : nxt ψ 0 = head (fun i : Fin n => ψ i.succ) := by
      unfold nxt head
      by_cases h : 0 < n
      · rw [dif_pos (by simp; omega), dif_pos h]; congr 1
      · rw [dif_neg (by simp; omega), dif_neg h]
    simp_rw [h1]
    rw [prod_ev_nxt n, ← h2, ← ev_mul_char, div_mul_cancel]
    simp [head]

variable {r t : ℕ}

theorem castAdd_eq (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by ext; simp
theorem natAdd_eq (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by ext; simp

theorem emb_ll (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  rw [castAdd_eq, castAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

theorem emb_lr (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) (j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

theorem emb_rl (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin t) (j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

theorem emb_rr (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.natAdd r j) = b.val i j := by
  rw [natAdd_eq, natAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

def eqvL (i : Fin r) : {y : Fin r // y ≤ i} ≃ {x : Fin (r + t) // x ≤ Fin.castAdd t i} :=
  Equiv.ofBijective (fun y : {y : Fin r // y ≤ i} => (⟨Fin.castAdd t y.1, by
      have := y.2; simp only [Fin.le_def, Fin.coe_castAdd] at this ⊢; omega⟩ :
        {x : Fin (r + t) // x ≤ Fin.castAdd t i})) (by
    constructor
    · rintro ⟨y, hy⟩ ⟨z, hz⟩ h
      simp only [Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd] at h
      exact Subtype.ext (Fin.ext h)
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ i := by simpa [Fin.le_def] using hx
      exact ⟨⟨⟨x, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp⟩)

theorem eqvL_val (i : Fin r) (y : {y : Fin r // y ≤ i}) : ((eqvL (t := t) i y) : Fin (r + t)) = Fin.castAdd t y.1 := rfl

def eqvR (j : Fin t) : Fin r ⊕ {y : Fin t // y ≤ j} ≃ {x : Fin (r + t) // x ≤ Fin.natAdd r j} :=
  Equiv.ofBijective (Sum.elim (fun i : Fin r => (⟨Fin.castAdd t i, by
        simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))
      (fun y : {y : Fin t // y ≤ j} => (⟨Fin.natAdd r y.1, by
        have := y.2; simp only [Fin.le_def, Fin.coe_natAdd] at this ⊢; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))) (by
    constructor
    · intro u v h
      rcases u with y | y <;> rcases v with z | z <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd,
          Fin.coe_natAdd] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · have := y.2; omega
      · have := z.2; omega
      · exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ r + j := by simpa [Fin.le_def] using hx
      by_cases h : (x : ℕ) < r
      · exact ⟨Sum.inl ⟨x, h⟩, by ext; simp⟩
      · exact ⟨Sum.inr ⟨⟨x - r, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp; omega⟩)

theorem eqvR_inl (j : Fin t) (i : Fin r) : ((eqvR j (Sum.inl i)) : Fin (r + t)) = Fin.castAdd t i := rfl
theorem eqvR_inr (j : Fin t) (y : {y : Fin t // y ≤ j}) : ((eqvR (r := r) j (Sum.inr y)) : Fin (r + t)) = Fin.natAdd r y.1 := rfl

theorem minor_castAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.castAdd t i) = minor a i := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvL i)]
  congr 1
  ext y z
  simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvL_val, emb_ll]

theorem minor_natAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (j : Fin t) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.natAdd r j) = a.val.det * minor b j := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvR j)]
  rw [show ((emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val.toSquareBlockProp fun x => x ≤ Fin.natAdd r j).submatrix (eqvR j) (eqvR j)
      = fromBlocks a.val 0 0 (b.val.toSquareBlockProp fun x => x ≤ j) by
    ext (y | y) (z | z) <;> simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvR_inl, eqvR_inr,
      emb_ll, emb_lr, emb_rl, emb_rr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply]]
  rw [det_fromBlocks_zero₂₁]

theorem minor_last {r : ℕ} (a : GL (Fin (r + 1)) k) : minor a (Fin.last r) = a.val.det := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Fin.le_last x)).symm]
  congr 1

theorem nxt_natAdd (ψ : Fin (r + t) → kˣ →* ℂˣ) (j : Fin t) :
    nxt ψ (Fin.natAdd r j) = nxt (fun i => ψ (Fin.natAdd r i)) j := by
  unfold nxt
  by_cases h : (j : ℕ) + 1 < t
  · rw [dif_pos (by simp; omega), dif_pos h]; congr 1
  · rw [dif_neg (by simp; omega), dif_neg h]

theorem nxt_castAdd_castSucc {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) (i : Fin r) :
    nxt ψ (Fin.castAdd t i.castSucc) = nxt (fun i => ψ (Fin.castAdd t i)) i.castSucc := by
  unfold nxt
  rw [dif_pos (by simp; omega), dif_pos (by simp)]
  congr 1

theorem nxt_castAdd_last {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) :
    nxt ψ (Fin.castAdd t (Fin.last r)) = head (fun j : Fin t => ψ (Fin.natAdd (r + 1) j)) := by
  unfold nxt head
  by_cases h : 0 < t
  · rw [dif_pos (by simp; omega), dif_pos h]; congr 1
  · rw [dif_neg (by simp; omega), dif_neg h]

theorem nxt_last_one {r : ℕ} (φ : Fin (r + 1) → kˣ →* ℂˣ) : nxt φ (Fin.last r) = 1 := by
  unfold nxt; rw [dif_neg (by simp)]

theorem first_part : ∀ (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k),
    (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
      ev (head fun j : Fin t => ψ (Fin.natAdd r j)) a.val.det = theta (fun i => ψ (Fin.castAdd t i)) a
  | 0, t, ψ, a => by simp [theta, Matrix.det_isEmpty, ev_at_one]
  | r + 1, t, ψ, a => by
    unfold theta
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc, minor_last, nxt_castAdd_last,
      nxt_last_one, ← ev_mul_char, div_mul_cancel, div_one]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [nxt_castAdd_castSucc]

end GlobalTheory.PsType.BlockTheta

open GlobalTheory.PsType.BlockTheta in

theorem GlobalTheory.PsType.theta_emb₂_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  intro k _ _ _ _ r t ψ hord a ha b hb
  have hord₂ : Ordered (fun i => ψ (Fin.natAdd r i)) := by
    intro i a' b' j h1 h2 h3 x hx
    exact hord (Fin.natAdd r i) (Fin.natAdd r a') (Fin.natAdd r b') (Fin.natAdd r j) (by rw [Fin.le_def] at h1 ⊢; simp only [Fin.coe_natAdd]; omega) (by rw [Fin.le_def] at h2 ⊢; simp only [Fin.coe_natAdd]; omega)
      (by rw [Fin.le_def] at h3 ⊢; simp only [Fin.coe_natAdd]; omega) x hx
  have hda : valuation k a.val.det = 1 := val_det_of_mem_KO ha.1
  have hsplit : theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) =
      (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
        ((∏ j : Fin t, ev ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) a.val.det) *
          theta (fun i => ψ (Fin.natAdd r i)) b) := by
    unfold theta
    rw [Fin.prod_univ_add]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [minor_castAdd]
    · rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [minor_natAdd, nxt_natAdd]
      by_cases hT : Triv ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) 1
      · rw [ev_of_triv_one _ hT, ev_of_triv_one _ hT, ev_of_triv_one _ hT, one_mul]
      · exact ev_mul_of_val _ hda ((GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k t _ hord₂ j hT).1 b hb)
  rw [hsplit, prod_ev_nxt, ← mul_assoc, first_part]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOneStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  first | exact @GlobalTheory.PsType.theta_one_and_near | exact GlobalTheory.PsType.theta_one_and_near | (intros; apply GlobalTheory.PsType.theta_one_and_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesUnipotentStripProperties
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_int_det {I : Type} [Fintype I] [DecidableEq I] {g : GL I k}
    (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) : g ∈ KO k I := by
  classical
  let M : Matrix I I 𝒪[k] := fun i j => ⟨g.val i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  have hmap : M.map (algebraMap 𝒪[k] k) = g.val := by
    ext i j
    rfl
  have hdet : IsUnit M.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_of_one' ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hd]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  refine ⟨u, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, hu]
  rfl

end GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem strip_off {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : y.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_neg h] at h0
  exact h0

theorem strip_on {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) :
    valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_pos h] at h0
  exact h0

theorem strip_lower {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : j < i) : y.val i j = 0 := by
  have hji : (j : ℕ) < (i : ℕ) := h
  rw [strip_off hy i j (fun hc => by omega), Matrix.one_apply_ne (ne_of_gt h)]

theorem strip_diag {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i : Fin n) : y.val i i = 1 := by
  rw [strip_off hy i i (fun hc => by omega), Matrix.one_apply_eq]

theorem strip_det {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m) :
    y.val.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => strip_lower hy i j h)]
  simp [strip_diag hy]

theorem strip_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ n ψ r ϖ hϖ hϖ1 hunif hcut
  have hent : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → ∀ i j : Fin n,
      ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → valuation k (y.val i j) ≤ 1 := by
    intro m y hy i j h
    rw [strip_off hy i j h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hdet1 : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → valuation k y.val.det = 1 := by
    intro m y hy
    rw [strip_det hy, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    refine (show y ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (y.val i j) from ⟨?_, ?_⟩)
    · refine mem_KO_of_int_det (fun i j => ?_) (hdet1 0 y hy)
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).1
        rwa [pow_zero, one_mul] at h0
      · exact hent 0 y hy i j h
    · intro i j hij
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).2
        rwa [pow_zero, one_mul] at h0
      · rw [strip_off hy i j h, Matrix.one_apply_ne (ne_of_lt hij)]
        exact triv_zero _
  · intro m y hy
    rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ y (fun _ => 1) (fun _ => by simp) (fun i => by simp [strip_diag hy i])
      (Or.inr fun i j h => strip_lower hy i j h)]
    simp
  · intro y hy
    refine mem_KO_of_int_det (fun i j => ?_) (hdet1 1 y hy)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · obtain ⟨h1, h2⟩ := strip_on hy i j h
      rw [pow_one] at h1 h2
      have hlt : valuation k (ϖ * y.val i j) < 1 := by
        refine lt_of_le_of_ne h1 fun heq => hcut i j h.1 h.2 ?_
        exact triv_mono _ _ _ (le_of_eq (by rw [heq, map_one])) h2
      have hle := hunif _ hlt
      rw [map_mul] at hle
      have hpos : 0 < valuation k ϖ := zero_lt_iff.2 ((map_ne_zero _).2 hϖ)
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    · exact hent 1 y hy i j h
  · intro z hz m y
    set d : Fin n → k := fun i : Fin n => if (i : ℕ) < r then ϖ else 1 with hd_def
    have hd : ∀ i, d i ≠ 0 := by
      intro i
      simp only [hd_def]
      split_ifs
      exacts [hϖ, one_ne_zero]
    have hzz : z.val * (z⁻¹).val = 1 := by simp
    have hzinv : (z⁻¹).val = Matrix.diagonal (fun i => (d i)⁻¹) := by
      calc (z⁻¹).val = (Matrix.diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by
            rw [hz, Matrix.diagonal_mul_diagonal]
            rw [show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : k) from funext fun i => inv_mul_cancel₀ (hd i)]
            rw [Matrix.diagonal_one, one_mul]
        _ = Matrix.diagonal (fun i => (d i)⁻¹) := by rw [mul_assoc, hzz, mul_one]
    have hentry : ∀ i j : Fin n, (z * y * z⁻¹).val i j = d i * y.val i j * (d j)⁻¹ := by
      intro i j
      rw [Units.val_mul, Units.val_mul, hz, hzinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [strip, Set.mem_ofPred_eq, hentry]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [if_pos h, if_pos h]
      have hdi : d i = ϖ := by simp only [hd_def]; rw [if_pos h.1]
      have hdj : d j = 1 := by simp only [hd_def]; rw [if_neg (by omega)]
      rw [hdi, hdj, show ϖ ^ m * (ϖ * y.val i j * (1 : k)⁻¹) = ϖ ^ (m + 1) * y.val i j by ring]
    · rw [if_neg h, if_neg h]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, mul_comm (d i), mul_inv_cancel_right₀ (hd i)]
      · rw [Matrix.one_apply_ne hij]
        simp [hd i, hd j]

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangularStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNQ.qAll_affine | exact GlobalTheory.FNQ.qAll_affine | (intros; apply GlobalTheory.FNQ.qAll_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphicStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_differentiableOn_quotient_of_integral : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  first | exact @GlobalTheory.quotient_integral_holomorphic | exact GlobalTheory.quotient_integral_holomorphic | (intros; apply GlobalTheory.quotient_integral_holomorphic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueAlgebraicPolynomialDivisibleStatement
section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_algebraic_polynomial_divisible : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  first | exact @GlobalTheory.K5.exists_int_poly_root_mod_p | exact GlobalTheory.K5.exists_int_poly_root_mod_p | (intros; apply GlobalTheory.K5.exists_int_poly_root_mod_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquivStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T → (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E))) (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  first | exact @GlobalTheory.KZ.ssPot_transport | exact GlobalTheory.KZ.ssPot_transport | (intros; apply GlobalTheory.KZ.ssPot_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSqStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_eq_one_of_mem_ker_commutator_central_ext_sl : ∀ (l n p a : ℕ), l.Prime → p.Prime → 5 ≤ p → p ≠ l → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ a))), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  first | exact @GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | exact GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | (intros; apply GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEqStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  first | exact @GlobalTheory.FNCong.cong_iff_dg | exact GlobalTheory.FNCong.cong_iff_dg | (intros; apply GlobalTheory.FNCong.cong_iff_dg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEqStatement
section
open GlobalTheory.K5 GlobalTheory.Glue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_kaehlerD_reparametrization_eq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  first | exact @GlobalTheory.Glue.DPsi.smul_D_psi | exact GlobalTheory.Glue.DPsi.smul_D_psi | (intros; apply GlobalTheory.Glue.DPsi.smul_D_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelMassDegreeTypeLeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelMass_degreeType_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (μ : Multiset ℕ), (mass g N fun f => degType g f = μ) ≤ (∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * (μ.count d).factorial))⁻¹ := by
  first | exact @GlobalTheory.BadShare.mass_degType_le | exact GlobalTheory.BadShare.mass_degType_le | (intros; apply GlobalTheory.BadShare.mass_degType_le <;> assumption)
end


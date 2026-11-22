import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarmonicColumnOperatorEndMemOfUnitaryStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumSmulMemOfSumZpowSmulMem

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1))) ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1))) := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColEInvMulAffPt
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.ColumnSupport

theorem colE_inv_mul_affPt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    {c p : ℕ} (hp : p < c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (p + 1) rs} → k) (r : n) :
    (((colE c (p + 1) β)⁻¹).val * affPt (p + 1) x₀ e) (Sum.inl r) (Sum.inr ⟨p, by omega⟩) = -β r := by
  have hv : ((colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0)) 0 1 := rfl
  have h1 : ∀ s : n, affPt (p + 1) x₀ e (Sum.inl s) (Sum.inr ⟨p, by omega⟩) = 0 := by
    intro s
    simp [affPt, basePt, Free]
  have h2 : affPt (p + 1) x₀ e (Sum.inr ⟨p, hp⟩) (Sum.inr ⟨p, by omega⟩) = 1 := by
    simp [affPt, basePt, Free]
  rw [hv, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [h1, mul_zero, Finset.sum_const_zero, zero_add, fromBlocks_apply₁₂]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : Fin c)]
  · simp [h2]
  · intro j _ hj
    have : j.val ≠ p := fun e => hj (Fin.ext e)
    simp [this]
  · simp

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ), ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∃ K : Set (n → k), IsCompact K ∧ ∀ β, β ∉ K → ∀ χ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => χ y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.colE c (p + 1) β) Φ y) = 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp ψ ν μ Φ hΦ
  have hcs : HasCompactSupport Φ := (show IsLocallyConstant Φ ∧ HasCompactSupport Φ from hΦ).2
  let q : Fin (c + 1) := ⟨p, by omega⟩
  refine ⟨(fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => fun r => -z (Sum.inl r) (Sum.inr q)) '' tsupport Φ,
    hcs.isCompact.image (continuous_pi fun r => (continuous_apply_apply _ _).neg), ?_⟩
  intro β hβ χ
  funext x
  unfold _root_.GlobalTheory.RootEx.opE
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
  have hentry : ∀ r, ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e) (Sum.inl r) (Sum.inr q) = -β r := by
    intro r
    rw [_root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp [q, Matrix.mul_apply, Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, _root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => if_neg (fun h => hb (Fin.ext h))) (by simp)]
    simp
  have hzero : Φ ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e * ((1 : GL (n' ⊕ Fin (c + 1)) k) : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = 0 := by
    by_contra h
    apply hβ
    refine ⟨_, subset_tsupport _ h, ?_⟩
    funext r
    simp only [Units.val_one, Matrix.mul_one]
    rw [hentry r, neg_neg]
  unfold _root_.GlobalTheory.SplitWeil.om
  simp only [Pi.zero_apply]
  rw [hzero]
  simp

end GlobalTheory.RootEx.ColumnSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactModStabilizer
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.PairingOne

section Alg
variable {k : Type*} [Field k] {m : Type*} [Fintype m] [DecidableEq m]

def rowMat (o j : m) (l y : m → k) : Matrix m m k := fun r c =>
  if r = o then l c else (if Equiv.swap o j r = c then 1 else 0) - y (Equiv.swap o j r) * l c

def colMat (o j : m) (l y : m → k) : Matrix m m k := fun c r =>
  if r = o then y c else
    (if Equiv.swap o j r = c then 1 else 0) - (if j = c then 1 else 0) * (l (Equiv.swap o j r) / l j)

end Alg

variable {k : Type*} [Field k] [ValuativeRel k] {m : Type*} [Fintype m] [DecidableEq m]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_bounded (t : ValueGroupWithZero k) :
    IsCompact {w : GL m k | (∀ a b, valuation k (w.val a b) ≤ t) ∧ ∀ a b, valuation k ((w⁻¹).val a b) ≤ t} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} := by
    have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k t
    have e : {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} =
        (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix m m k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.PairingOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasisStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F), (∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) → f = g := by
  first | exact @GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | exact GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | (intros; apply GlobalTheory.continuousMultilinearMap_ext_hilbertBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergSubgroupFourierJacobiCommutator
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSubgroup

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def zM (c p : ℕ) (t : k) : Matrix (Fin c) (Fin c) k :=
  Matrix.of fun l i => if l.val + 1 = p ∧ i.val + 1 = p + 1 then t else 0

def hM (c p : ℕ) (u β : n → k) (t : k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  fromBlocks 1 (ExchangeSupport.colM c (p + 1) β) (ExchangeSupport.rowM c p u) (1 + zM c p t)

theorem zM_add (s t : k) : zM c p (s + t) = zM c p s + zM c p t := by
  ext l i
  simp only [zM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem zM_zero : zM c p (0 : k) = 0 := by
  ext l i
  simp [zM]

theorem zM_mul (s t : k) : zM c p s * zM c p t = 0 := by
  ext l i
  simp only [Matrix.mul_apply, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem col_mul_zM (β : n → k) (t : k) : ExchangeSupport.colM c (p + 1) β * zM c p t = 0 := by
  ext r i
  simp only [Matrix.mul_apply, ExchangeSupport.colM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem zM_mul_row (u : n → k) (t : k) : zM c p t * ExchangeSupport.rowM c p u = 0 := by
  ext l s
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [DecidableEq n] in
theorem row_mul_col (u β : n → k) :
    ExchangeSupport.rowM c p u * ExchangeSupport.colM c (p + 1) β = zM c p (u ⬝ᵥ β) := by
  ext l i
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, ExchangeSupport.colM, zM, Matrix.of_apply]
  by_cases hl : l.val + 1 = p <;> by_cases hi : i.val + 1 = p + 1 <;> simp [hl, hi, dotProduct]

omit [Fintype n] [DecidableEq n] in
theorem row_add (u w : n → k) : ExchangeSupport.rowM c p (u + w) =
    ExchangeSupport.rowM c p u + ExchangeSupport.rowM c p w := by
  ext l s
  simp only [ExchangeSupport.rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem col_add (u w : n → k) : ExchangeSupport.colM c p (u + w) =
    ExchangeSupport.colM c p u + ExchangeSupport.colM c p w := by
  ext r i
  simp only [ExchangeSupport.colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem row_zero : ExchangeSupport.rowM c p (0 : n → k) = 0 := by
  ext l s
  simp [ExchangeSupport.rowM]

omit [Fintype n] [DecidableEq n] in
theorem col_zero : ExchangeSupport.colM c p (0 : n → k) = 0 := by
  ext r i
  simp [ExchangeSupport.colM]

theorem hM_mul (u β u' β' : n → k) (t t' : k) :
    hM c p u β t * hM c p u' β' t' = hM c p (u + u') (β + β') (t + t' + u ⬝ᵥ β') := by
  simp only [hM, Matrix.fromBlocks_multiply]
  congr 1
  · rw [ExchangeSupport.colM_mul_rowM, Matrix.one_mul, add_zero]
  · rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, col_mul_zM, add_zero, col_add]
    abel
  · rw [Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, zM_mul_row, add_zero, row_add]
  · rw [row_mul_col]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, zM_mul, zM_add]
    abel

omit [Fintype n] in
theorem hM_zero : hM c p (0 : n → k) 0 0 = 1 := by
  rw [hM, row_zero, col_zero, zM_zero, add_zero, Matrix.fromBlocks_one]

theorem rowE_eq (u : n → k) : (rowE c p u).val = hM c p u 0 0 := by
  rw [ExchangeSupport.rowE_val, hM, col_zero, zM_zero, add_zero]

theorem colE_eq (β : n → k) : (colE c (p + 1) β).val = hM c p 0 β 0 := by
  rw [ExchangeSupport.colE_val, hM, row_zero, zM_zero, add_zero]

theorem cenM_eq (t : k) : cenM n c p t = hM c p 0 0 t := by
  rw [hM, row_zero, col_zero]
  rfl

theorem prod_eq (u β : n → k) (t : k) :
    (rowE c p u).val * (colE c (p + 1) β).val * cenM n c p t = hM c p u β (u ⬝ᵥ β + t) := by
  rw [rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul]
  simp only [add_zero, zero_add, dotProduct_zero]

def Heisenberg₂ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | ∃ (u β : n → k) (t : k), g.val = hM c p u β t}
  one_mem' := ⟨0, 0, 0, hM_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨u, β, t, hg⟩ ⟨u', β', t', hh⟩
    exact ⟨_, _, _, by rw [Units.val_mul, hg, hh, hM_mul]⟩
  inv_mem' := by
    rintro g ⟨u, β, t, hg⟩
    refine ⟨-u, -β, u ⬝ᵥ β - t, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hg, hM_mul, ← hM_zero (p := p)]
    simp

theorem mem_N_of_val {g : GL (n ⊕ Fin c) k} {β : n → k} {t : k} (hg : g.val = hM c p 0 β t) :
    g ∈ N k n c p := by
  show g ∈ Subgroup.closure {g | InN p g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [hg, hM, row_zero]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₁₂, ExchangeSupport.colM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply, zM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp [Matrix.one_apply]

private theorem eMat_mem_N_succ (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  show rowE c p u ∈ Subgroup.closure {g | InN (p + 1) g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [ExchangeSupport.rowE_val]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₁, ExchangeSupport.rowM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp [Matrix.one_apply]

theorem heis_le : Heisenberg₂ k n c p ≤ NFJ k n c p := by
  rintro g ⟨u, β, t, hg⟩
  have hinv : rowE c p u * rowE c p (-u) = 1 := by
    rw [← ExchangeSupport.rowE_add, add_neg_cancel, ExchangeSupport.rowE_zero]
  have hsplit : g = rowE c p u * (rowE c p (-u) * g) := by
    rw [← mul_assoc, hinv, one_mul]
  have hrest : rowE c p (-u) * g ∈ N k n c p := by
    refine mem_N_of_val (β := β) (t := t - u ⬝ᵥ β) ?_
    rw [Units.val_mul, hg, rowE_eq, hM_mul]
    simp only [neg_add_cancel, zero_add, neg_dotProduct]
    ring_nf
  rw [hsplit]
  exact Subgroup.mul_mem _ (le_sup_right (a := N k n c p) (eMat_mem_N_succ u))
    (le_sup_left (b := N k n c (p + 1)) hrest)

end

theorem heisenberg_subgroup : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k), g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧ ∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val = cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val := by
  intro k _ n _ _ c ρ _ _
  refine ⟨⟨Heisenberg₂ k n c ρ, heis_le, fun g => ?_⟩, fun u β₀ => ?_⟩
  · constructor
    · rintro ⟨u, β, t, hg⟩
      refine ⟨u, β, t - u ⬝ᵥ β, ?_⟩
      rw [prod_eq, hg]
      congr 1
      ring
    · rintro ⟨u, β, t, hg⟩
      exact ⟨u, β, u ⬝ᵥ β + t, by rw [hg, prod_eq]⟩
  · rw [Units.val_mul, Units.val_mul, rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul, hM_mul]
    simp only [add_zero, zero_add, dotProduct_zero, zero_dotProduct]

end GlobalTheory.RootEx.HeisenbergSubgroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsHilbertSchmidtOrthonormalApplyStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  first | exact @GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | exact GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | (intros; apply GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}

theorem isSelfDual_iff_vol (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp

theorem exists_isSelfDual_of_hasConductor (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']

theorem isUnitVol_iff_isSelfDual (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · exact isSelfDual_of_isUnitVol ν h
  · intro hsd
    have := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩

theorem selfDual_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν

end GlobalTheory.SplitWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SBConv

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem eventually_translate {F : G → ℂ} (hF : F ∈ SB G) :
    ∀ᶠ x in nhds (0 : G), ∀ g, F (g - x) = F g := by
  have hlc : IsLocallyConstant F := hF.1
  have hK : IsCompact (tsupport F) := hF.2
  have hz : ∀ z, z ∉ tsupport F → F z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport F h)
  have step : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - x) = F y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hy := hlc.eventually_eq y
    have h1 : Filter.Tendsto (fun p : G × G => p.2 - p.1) (nhds ((0 : G), y)) (nhds y) := by
      simpa using (continuous_snd.tendsto ((0 : G), y)).sub (continuous_fst.tendsto ((0 : G), y))
    have h2 : Filter.Tendsto (fun p : G × G => p.2) (nhds ((0 : G), y)) (nhds y) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have step' : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - -x) = F y :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero).eventually step
  filter_upwards [step, step'] with x hx hx' g
  by_cases hg : g ∈ tsupport F
  · exact hx g hg
  · rw [hz g hg]
    by_cases hg' : g - x ∈ tsupport F
    · have h := hx' (g - x) hg'
      rw [sub_neg_eq_add, sub_add_cancel, hz g hg] at h
      exact h.symm
    · exact hz _ hg'

def translate (Ψ : SB G) (y : G) : SB G :=
  ⟨fun x => Ψ.1 (x - y), Ψ.2.1.comp_continuous (continuous_sub_right y),
    Ψ.2.2.comp_homeomorph (Homeomorph.subRight y)⟩

theorem isLocallyConstant_translate (Ψ : SB G) : IsLocallyConstant (translate Ψ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hmap : Filter.Tendsto (fun y' : G => y' - y) (nhds y) (nhds 0) := by
    simpa using (continuous_id.tendsto y).sub_const y
  filter_upwards [hmap.eventually (eventually_translate Ψ.2)] with y' hy'
  apply Subtype.ext
  funext x
  show Ψ.1 (x - y') = Ψ.1 (x - y)
  have h := hy' (x - y)
  rwa [sub_sub_sub_cancel_right] at h

theorem exists_conv [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (Φ Ψ : SB G) :
    ∃ w : SB G, (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂μ) ∧
      ∀ l : SB G →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (translate Ψ y) ∂μ := by
  have hT : IsLocallyConstant (fun y => Φ.1 y • translate Ψ y) :=
    IsLocallyConstant.comp₂ Φ.2.1 (isLocallyConstant_translate Ψ) (fun c f => c • f)
  have hz : ∀ y, y ∉ tsupport Φ.1 → Φ.1 y • translate Ψ y = 0 := by
    intro y hy
    have h0 : Φ.1 y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    rw [h0, zero_smul]
  obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact G μ (SB G)
    (fun y => Φ.1 y • translate Ψ y) hT (tsupport Φ.1) Φ.2.2.isCompact hz
  refine ⟨w, fun x => ?_, fun l => ?_⟩
  · exact hw ((LinearMap.proj x).comp (SB G).subtype)
  · rw [hw l]
    simp only [map_smul, smul_eq_mul]

end Abstract

theorem exists_convolution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ ν _ Φ Ψ
  have : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have : ν.Regular := inferInstance
  have : ν.IsNegInvariant := inferInstance
  obtain ⟨w, hw1, hw2⟩ := exists_conv (Measure.pi fun _ : n => ν) Φ Ψ
  refine ⟨translate Ψ, w, fun y x => rfl, hw1, fun x => ?_, hw2⟩
  rw [hw1 x]
  have h := integral_sub_left_eq_self (fun y => Φ.1 (x - y) * Ψ.1 y) (Measure.pi fun _ : n => ν) x
  simp only [sub_sub_cancel] at h
  refine h.trans ?_
  congr 1
  funext y
  exact mul_comm _ _

end GlobalTheory.SBConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarmonicColumnOperatorEndMemOfUnitaryStableStatement
section
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicColumnOperatorEnd_mem_of_unitary_stable : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {p q n : ℕ} (W : Submodule ℂ (GlobalTheory.Harm.Poly ℂ ι p q (Fin n))), (∀ g : ι → GL (Fin n) ℂ, (∀ t, (g t : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ w ∈ W, GlobalTheory.Harm.colActHom g w ∈ W) → ∀ (t : ι) (k l : Fin n), ∀ w ∈ W, GlobalTheory.Harm.colLie ℂ p q t k l w ∈ W := by
  first | exact @GlobalTheory.Harm.colLie_mem_of_unitary_stable | exact GlobalTheory.Harm.colLie_mem_of_unitary_stable | (intros; apply GlobalTheory.Harm.colLie_mem_of_unitary_stable <;> assumption)
end


import Mathlib

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
section
open MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical

section Algebra

variable {k : Type} [Field k] {r : ℕ} (b : Fin r → ℕ)

variable (k) in

def lieRadical : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, ¬ b i < b j → X i j = 0}
  add_mem' := by
    intro X Y hX hY i j h
    simp [hX i j h, hY i j h]
  zero_mem' := by intro i j _; rfl
  smul_mem' := by
    intro c X hX i j h
    simp [hX i j h]

variable {b}

theorem mul_mem_lieRadical {A X : Matrix (Fin r) (Fin r) k} (hA : A.BlockTriangular b)
    (hX : X ∈ lieRadical k b) : A * X ∈ lieRadical k b := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b l < b i
  · rw [hA hl, zero_mul]
  · rw [hX l j (by omega), mul_zero]

theorem mem_lieRadical_mul {A X : Matrix (Fin r) (Fin r) k} (hX : X ∈ lieRadical k b)
    (hA : A.BlockTriangular b) : X * A ∈ lieRadical k b := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b j < b l
  · rw [hA hl, mul_zero]
  · rw [hX i l (by omega), zero_mul]

theorem blockTriangular_inv {α : Type} [LinearOrder α] {c : Fin r → α} {g : GL (Fin r) k}
    (hg : (g : Matrix (Fin r) (Fin r) k).BlockTriangular c) :
    ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular c := by
  letI := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg

theorem blockTriangular_of_sub_one {A : Matrix (Fin r) (Fin r) k} (h : A - 1 ∈ lieRadical k b) :
    A.BlockTriangular b := by
  intro i j hij
  have h1 := h i j (by omega)
  have hne : i ≠ j := by rintro rfl; omega
  simpa [Matrix.one_apply_ne hne] using h1

variable (k b) in

def radical : Subgroup (GL (Fin r) k) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) k) - 1 ∈ lieRadical k b}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    have e : ((g * h : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1
        = (g : Matrix (Fin r) (Fin r) k) * ((h : Matrix (Fin r) (Fin r) k) - 1)
          + ((g : Matrix (Fin r) (Fin r) k) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one]; abel
    show _ ∈ lieRadical k b
    rw [e]
    exact add_mem (mul_mem_lieRadical (blockTriangular_of_sub_one hg) hh) hg
  inv_mem' := by
    intro g hg
    have e : ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1
        = -(((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
          * ((g : Matrix (Fin r) (Fin r) k) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul]; abel
    show _ ∈ lieRadical k b
    rw [e]
    exact neg_mem (mul_mem_lieRadical (blockTriangular_inv (blockTriangular_of_sub_one hg)) hg)

variable (k b) in

def levi : Subgroup (GL (Fin r) k) where
  carrier := {g | ∀ i j, b i ≠ b j → (g : Matrix (Fin r) (Fin r) k) i j = 0}
  one_mem' := by
    intro i j h
    have hne : i ≠ j := by rintro rfl; exact h rfl
    simp [Matrix.one_apply_ne hne]
  mul_mem' := by
    intro g h hg hh i j hij
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : b i = b l
    · rw [hh l j (by omega), mul_zero]
    · rw [hg i l hl, zero_mul]
  inv_mem' := by
    intro g hg i j hij
    have h1 : (g : Matrix (Fin r) (Fin r) k).BlockTriangular b := fun i j h => hg i j (by omega)
    have h2 : (g : Matrix (Fin r) (Fin r) k).BlockTriangular (OrderDual.toDual ∘ b) :=
      fun i j h => hg i j (ne_of_lt h)
    rcases lt_or_gt_of_ne hij with h | h
    · exact blockTriangular_inv h2 h
    · exact blockTriangular_inv h1 h

theorem levi_blockTriangular (δ : levi k b) :
    ((δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular b :=
  fun i j h => δ.2 i j (by omega)

def adRadical (δ : levi k b) : lieRadical k b →ₗ[k] lieRadical k b where
  toFun X := ⟨((δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (X : Matrix (Fin r) (Fin r) k)
      * (((δ⁻¹ : levi k b) : GL (Fin r) k) : Matrix (Fin r) (Fin r) k),
    mem_lieRadical_mul (mul_mem_lieRadical (levi_blockTriangular δ) X.2)
      (levi_blockTriangular δ⁻¹)⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp

theorem conj_mem_radical (δ : levi k b) {n : GL (Fin r) k} (hn : n ∈ radical k b) :
    (δ : GL (Fin r) k)⁻¹ * n * δ ∈ radical k b := by
  have e : (((δ : GL (Fin r) k)⁻¹ * n * δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1
      = (((δ⁻¹ : levi k b) : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        * ((n : Matrix (Fin r) (Fin r) k) - 1) * ((δ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
    rw [mul_sub, sub_mul, mul_one, Subgroup.coe_inv, Units.inv_mul, Units.val_mul, Units.val_mul]
  show _ ∈ lieRadical k b
  rw [e]
  exact mem_lieRadical_mul (mul_mem_lieRadical (levi_blockTriangular δ⁻¹) hn)
    (levi_blockTriangular δ)

def twistedCommutator (δ : levi k b) (n : radical k b) : radical k b :=
  ⟨(δ : GL (Fin r) k)⁻¹ * (n : GL (Fin r) k)⁻¹ * δ * n,
    mul_mem (conj_mem_radical δ (inv_mem n.2)) n.2⟩

end Algebra

noncomputable def modulus (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
    [LocallyCompactSpace k] (x : k) : ℝ :=
  open Classical in
  if h : x = 0 then 0 else (distribHaarChar k (Units.mk0 x h) : ℝ)

def UnipotentChangeOfVariables : Prop :=
  ∀ (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] [T2Space k]
    [LocallyCompactSpace k] [SecondCountableTopology k], ¬ DiscreteTopology k →
    ∀ (r : ℕ) (b : Fin r → ℕ) (δ : levi k b),
      Function.Bijective (adRadical δ - LinearMap.id : lieRadical k b →ₗ[k] lieRadical k b) →
      IsHomeomorph (twistedCommutator δ) ∧
      ∀ [MeasurableSpace (radical k b)] [BorelSpace (radical k b)]
        (μ : Measure (radical k b)) [μ.IsHaarMeasure] (φ : radical k b → ℂ),
        Continuous φ → HasCompactSupport φ →
        ∫ n, φ (twistedCommutator δ n) ∂μ =
          (((modulus k (LinearMap.det
            (LinearMap.id - adRadical δ⁻¹ : lieRadical k b →ₗ[k] lieRadical k b)))⁻¹ : ℝ) : ℂ)
            * ∫ n, φ n ∂μ

def RegularLeviNoEigenvalueOne : Prop :=
  ∀ (k : Type) [Field k] (r : ℕ) (b : Fin r → ℕ) (γ m : levi k b),
    ((γ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).charpoly.Separable →
    ¬ Module.End.HasEigenvalue (adRadical (m⁻¹ * γ * m)) 1

example : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ∈ lieRadical ℝ (fun i : Fin 2 => (i : ℕ)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

example (h : UnipotentChangeOfVariables) (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → ℕ) :
    (∀ δ : levi ℝ b, Function.Bijective
      (adRadical δ - LinearMap.id : lieRadical ℝ b →ₗ[ℝ] lieRadical ℝ b) →
        IsHomeomorph (twistedCommutator δ)) ∧
    (∀ δ : levi ℚ_[p] b, Function.Bijective
      (adRadical δ - LinearMap.id : lieRadical ℚ_[p] b →ₗ[ℚ_[p]] lieRadical ℚ_[p] b) →
        IsHomeomorph (twistedCommutator δ)) := by
  have nd : ∀ (k : Type) [NontriviallyNormedField k], ¬ DiscreteTopology k := fun k _ hk => by
    have h0 : (nhdsWithin (0 : k) {0}ᶜ).NeBot := inferInstance
    exact h0.ne (discreteTopology_iff_nhds_ne.1 hk 0)
  exact ⟨fun δ hδ => (h ℝ (nd ℝ) r b δ hδ).1, fun δ hδ => (h ℚ_[p] (nd _) r b δ hδ).1⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
section
open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

def gaussBinom (q m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun j => Nat.casesOn j 1 fun _ => 0)
    (fun m b j => Nat.casesOn j 1 fun j => b (j + 1) + q ^ (m - j) * b j) m

open Module in
@[simp] theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right (q m : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m 0 = 1 := by
  cases m <;> rfl

@[simp] theorem gaussBinom_zero_succ (q j : ℕ) : gaussBinom q 0 (j + 1) = 0 := rfl

theorem gaussBinom_succ_succ (q m j : ℕ) :
    gaussBinom q (m + 1) (j + 1) = gaussBinom q m (j + 1) + q ^ (m - j) * gaussBinom q m j := rfl

open Module in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero (q : ℕ) :
    ∀ m j : ℕ, m < j → _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rfl
  | succ m ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, ih (j + 1) (by omega), ih j (by omega)]
    simp

def SubspaceCount : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ),
    Nat.card {L : Submodule k V // finrank k L = j} = gaussBinom (Nat.card k) (finrank k V) j

def OverspaceCount : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (U : Submodule k (Fin r → k)) (j : ℕ),
    Nat.card {L : Submodule k (Fin r → k) // U ≤ L ∧ finrank k ((Fin r → k) ⧸ L) = j} =
      gaussBinom (Nat.card k) (r - finrank k U) j

def GaussFormula : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (R : Type) [CommRing R] (Y : R) (m : ℕ),
    ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (Nat.card k : R) ^ (j * (j - 1) / 2) *
          (gaussBinom (Nat.card k) m j : R) * Y ^ j =
      ∏ i ∈ Finset.range m, (1 - (Nat.card k : R) ^ i * Y)

def Statement : Prop := SubspaceCount ∧ OverspaceCount ∧ GaussFormula

example : gaussBinom 2 2 1 = 3 ∧ gaussBinom 2 3 1 = 7 ∧ gaussBinom 2 3 2 = 7 ∧
    gaussBinom 2 4 2 = 35 ∧ gaussBinom 3 4 2 = 130 := by decide

example (Y : ℤ) : ∑ j ∈ Finset.range (3 + 1),
    (-1 : ℤ) ^ j * ((3 : ℕ) : ℤ) ^ (j * (j - 1) / 2) * (gaussBinom 3 3 j : ℤ) * Y ^ j =
      ∏ i ∈ Finset.range 3, (1 - ((3 : ℕ) : ℤ) ^ i * Y) := by
  simp [Finset.sum_range_succ, Finset.prod_range_succ, gaussBinom_succ_succ]
  ring

end GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IntegralMatrixTranslation
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralMatrixTranslation

open Polynomial

section Defs

variable (O : Type) [CommRing O] (F : Type) [Field F] [Algebra O F]

def intGL (n : ℕ) : Subgroup (GL (Fin n) F) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap O F)).range

def IsIntMat {r n : ℕ} (u : Matrix (Fin r) (Fin n) F) : Prop :=
  ∀ a b, u a b ∈ (algebraMap O F).range

variable {F} in

def tDiag (p : Fˣ) (n j : ℕ) : GL (Fin n) F where
  val := Matrix.diagonal fun a => if (a : ℕ) < j then (p : F) else 1
  inv := Matrix.diagonal fun a => if (a : ℕ) < j then ((p⁻¹ : Fˣ) : F) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp

variable {F} in

def dcCosets {n : ℕ} (t : GL (Fin n) F) : Set (GL (Fin n) F ⧸ intGL O F n) :=
  {c | ∃ k₁ ∈ intGL O F n, ∃ k₂ ∈ intGL O F n, c = QuotientGroup.mk (k₁ * t * k₂)}

variable (R : Type) [CommRing R]

open Classical in

def phi0 (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) : R :=
  if IsIntMat O F u then 1 else 0

variable {O F}

theorem isIntMat_of_mem {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ intGL O F n) :
    IsIntMat O F (k : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨k₀, rfl⟩ := hk
  intro a b
  exact ⟨(k₀ : Matrix (Fin n) (Fin n) O) a b, rfl⟩

theorem IsIntMat.mul {l m n : ℕ} {u : Matrix (Fin l) (Fin m) F} {v : Matrix (Fin m) (Fin n) F}
    (hu : IsIntMat O F u) (hv : IsIntMat O F v) : IsIntMat O F (u * v) := by
  intro a b
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hu a c) (hv c b)

theorem phiZero_left_invariant {r n : ℕ} {k : GL (Fin r) F} (hk : k ∈ intGL O F r) (u : Matrix (Fin r) (Fin n) F) :
    phi0 O F R r n ((k : Matrix (Fin r) (Fin r) F) * u) = phi0 O F R r n u := by
  have h : IsIntMat O F ((k : Matrix (Fin r) (Fin r) F) * u) ↔ IsIntMat O F u := by
    refine ⟨fun h => ?_, fun h => (isIntMat_of_mem hk).mul h⟩
    have h2 := (isIntMat_of_mem ((intGL O F r).inv_mem hk)).mul h
    rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at h2
  unfold phi0
  rw [h]

theorem phiZero_right_invariant {r n : ℕ} {k : GL (Fin n) F} (hk : k ∈ intGL O F n) (u : Matrix (Fin r) (Fin n) F) :
    phi0 O F R r n (u * (k : Matrix (Fin n) (Fin n) F)) = phi0 O F R r n u := by
  have h : IsIntMat O F (u * (k : Matrix (Fin n) (Fin n) F)) ↔ IsIntMat O F u := by
    refine ⟨fun h => ?_, fun h => h.mul (isIntMat_of_mem hk)⟩
    have h2 := h.mul (isIntMat_of_mem ((intGL O F n).inv_mem hk))
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2
  unfold phi0
  rw [h]

variable (O F)

def leftTr (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) : GL (Fin r) F ⧸ intGL O F r → R :=
  Quotient.lift (fun g : GL (Fin r) F => phi0 O F R r n (((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * u))
    (fun g g' h => by
      have hk : g⁻¹ * g' ∈ intGL O F r := QuotientGroup.leftRel_apply.mp h
      have e : (g⁻¹ : GL (Fin r) F) = (g⁻¹ * g') * g'⁻¹ := by group
      show phi0 O F R r n _ = phi0 O F R r n _
      rw [e, Units.val_mul, Matrix.mul_assoc, phiZero_left_invariant R hk])

def rightTr (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) : GL (Fin n) F ⧸ intGL O F n → R :=
  Quotient.lift (fun h : GL (Fin n) F => phi0 O F R r n (u * (h : Matrix (Fin n) (Fin n) F)))
    (fun g g' h => by
      have hk : g⁻¹ * g' ∈ intGL O F n := QuotientGroup.leftRel_apply.mp h
      have e : g' = g * (g⁻¹ * g') := by group
      show phi0 O F R r n _ = phi0 O F R r n _
      rw [← phiZero_right_invariant R hk (u * (g : Matrix (Fin n) (Fin n) F)), Matrix.mul_assoc, ← Units.val_mul, ← e])

theorem leftTr_mk (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) (g : GL (Fin r) F) :
    leftTr O F R r n u (QuotientGroup.mk g) =
      phi0 O F R r n (((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * u) := rfl

theorem rightTr_mk (r n : ℕ) (u : Matrix (Fin r) (Fin n) F) (h : GL (Fin n) F) :
    rightTr O F R r n u (QuotientGroup.mk h) = phi0 O F R r n (u * (h : Matrix (Fin n) (Fin n) F)) := rfl

def opA (p : Fˣ) (r n k : ℕ) (u : Matrix (Fin r) (Fin n) F) : R :=
  ∑ᶠ c ∈ dcCosets O (tDiag p r k), leftTr O F R r n u c

def opB (p : Fˣ) (r n i : ℕ) (u : Matrix (Fin r) (Fin n) F) : R :=
  ∑ᶠ c ∈ dcCosets O (tDiag p n i)⁻¹, rightTr O F R r n u c

end Defs

def gaussCount (k : Type) [Field k] (m j : ℕ) : ℕ :=
  Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W = j}

def redRank (O : Type) [CommRing O] [IsLocalRing O] {r n : ℕ} (u₀ : Matrix (Fin r) (Fin n) O) : ℕ :=
  (u₀.map (IsLocalRing.residue O)).rank

def LocalTransfer : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    (ϖ : O) (p : Fˣ), Irreducible ϖ → (p : F) = algebraMap O F ϖ →
    ∀ (R : Type) [CommRing R] (r n : ℕ), r ≤ n →
      (∀ k ≤ r, (dcCosets O (tDiag p r k)).Finite) ∧
      (∀ i ≤ n, (dcCosets O (tDiag p n i)⁻¹).Finite) ∧
      (∀ k ≤ r,
        (∀ u₀ : Matrix (Fin r) (Fin n) O,
          opA O F R p r n k (u₀.map (algebraMap O F)) =
            (gaussCount (IsLocalRing.ResidueField O) (r - redRank O u₀) k : R)) ∧
        (∀ u : Matrix (Fin r) (Fin n) F, ¬ IsIntMat O F u → opA O F R p r n k u = 0)) ∧
      (∀ i ≤ n,
        (∀ u₀ : Matrix (Fin r) (Fin n) O,
          opB O F R p r n i (u₀.map (algebraMap O F)) =
            (gaussCount (IsLocalRing.ResidueField O) (n - redRank O u₀) i : R)) ∧
        (∀ u : Matrix (Fin r) (Fin n) F, ¬ IsIntMat O F u → opB O F R p r n i u = 0)) ∧
      ((∑ i ∈ Finset.range (n + 1),
          (-1) ^ i * (Nat.card (IsLocalRing.ResidueField O) : (Matrix (Fin r) (Fin n) F → R)[X]) ^ (i * (i - 1) / 2) *
            C (opB O F R p r n i) * X ^ i) =
        (∏ j ∈ Finset.range (n - r),
          (1 - (Nat.card (IsLocalRing.ResidueField O) : (Matrix (Fin r) (Fin n) F → R)[X]) ^ j * X)) *
        ∑ k ∈ Finset.range (r + 1),
          (-1) ^ k * (Nat.card (IsLocalRing.ResidueField O) : (Matrix (Fin r) (Fin n) F → R)[X]) ^ (k * (k - 1) / 2) *
            C (opA O F R p r n k) *
            ((Nat.card (IsLocalRing.ResidueField O) : (Matrix (Fin r) (Fin n) F → R)[X]) ^ (n - r) * X) ^ k)

theorem redRank_le (O : Type) [CommRing O] [IsLocalRing O] {r n : ℕ} (u₀ : Matrix (Fin r) (Fin n) O) :
    redRank O u₀ ≤ r := by
  simpa [redRank] using Matrix.rank_le_height (u₀.map (IsLocalRing.residue O))

example {F : Type} [Field F] (p : Fˣ) (n : ℕ) : tDiag p n 0 = 1 := by
  ext a b
  simp [tDiag]

example (k : Type) [Field k] (m : ℕ) : gaussCount k m 0 = 1 := by
  unfold gaussCount
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊥, finrank_bot _ _⟩, fun W => Subtype.ext (Submodule.finrank_eq_zero.mp W.2)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralMatrixTranslation
end
end


import Mathlib

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.Letters
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Dom (n : ℕ) (la : ℕ → ℤ) : Prop := ∀ m, m + 1 < n → la (m + 1) ≤ la m

def HStrip (n : ℕ) (mu mu' : ℕ → ℤ) : Prop :=
  (∀ m, m < n → mu m ≤ mu' m) ∧ ∀ m, m + 1 < n → mu' (m + 1) ≤ mu m

def Interl (n : ℕ) (la mu : ℕ → ℤ) : Prop := ∀ l, l < n → la l ≤ mu l ∧ mu (l + 1) ≤ la l

def wsize (n : ℕ) (la : ℕ → ℤ) : ℤ := ∑ m ∈ range n, la m

def tailPos (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : ℤ := ∑ m ∈ (range n).filter (fun m => u ≤ m), max (la m) 0

def tailNeg (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : ℤ :=
  ∑ m ∈ (range n).filter (fun m => u ≤ m), max (-(la (n - 1 - m))) 0

def weylDim (n : ℕ) (la : ℕ → ℤ) : ℝ :=
  ∏ j ∈ range n, ∏ i ∈ range j, (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ))

def fT (k' : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Icc 1 k', Real.log ((y + j) / j)

def fT' (k' : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Icc 1 k', 1 / (y + j)

structure Letters where
  r : ℕ
  K : ℕ
  Ns : ℕ
  vec : ℕ → Bool
  B : ℕ → ℕ

namespace Letters

def k (D : Letters) : ℕ := D.r + D.K

def n0 (D : Letters) : ℕ := D.Ns - D.r

def Wf (D : Letters) : Prop :=
  1 ≤ D.r ∧ 1 ≤ D.K ∧ 3 * D.r ≤ D.Ns ∧ (∀ i, 1 ≤ i → i ≤ D.r → D.vec i = true) ∧
  ∀ i, D.n0 < i → i ≤ D.Ns → D.vec i = true

def be (D : Letters) : ℕ := ∑ i ∈ Icc 1 D.n0, D.B i

def bePos (D : Letters) : ℕ := ∑ i ∈ (Icc 1 D.n0).filter (fun i => D.vec i = true), D.B i

def beNeg (D : Letters) : ℕ := ∑ i ∈ (Icc 1 D.n0).filter (fun i => D.vec i = false), D.B i

def latestV (D : Letters) (i : ℕ) : List ℕ :=
  (((List.range' 1 (min i D.n0)).filter fun l => D.vec l).reverse).map D.B

def latestC (D : Letters) (i : ℕ) : List ℕ :=
  (((List.range' 1 (min i D.n0)).filter fun l => !D.vec l).reverse).map D.B

def SPos (D : Letters) (u i : ℕ) : ℕ := ((D.latestV i).drop u).sum

def SNeg (D : Letters) (u i : ℕ) : ℕ := ((D.latestC i).drop u).sum

def Bo (D : Letters) (i : ℕ) : ℕ := (D.latestV (i - 1)).getD (D.r - 1 - (i - 1 - D.n0)) 0

def rankAA (D : Letters) : ℕ := ∏ i ∈ Icc 1 D.n0, (D.B i + D.k - 1).choose (D.k - 1)

abbrev Stages (D : Letters) : Type := Fin (D.Ns + 1) → Fin D.k → ℤ

def ent {D : Letters} (mu : D.Stages) (i m : ℕ) : ℤ :=
  if h : i < D.Ns + 1 ∧ m < D.k then mu ⟨i, h.1⟩ ⟨m, h.2⟩ else 0

def IsPATH (D : Letters) (mu : D.Stages) : Prop :=
  (∀ m, ent mu 0 m = 0) ∧ (∀ i, i ≤ D.Ns → Dom D.k (ent mu i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = true → HStrip D.k (ent mu (i - 1)) (ent mu i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = false → HStrip D.k (ent mu i) (ent mu (i - 1))) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = true →
    wsize D.k (ent mu i) - wsize D.k (ent mu (i - 1)) = D.B i) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = false →
    wsize D.k (ent mu (i - 1)) - wsize D.k (ent mu i) = D.B i) ∧
  ∀ i', 1 ≤ i' → i' ≤ D.r → ∀ m, m < i' → ent mu (D.n0 + i') m = D.be

def stLen (D : Letters) (i : ℕ) : ℕ := D.k - (i - D.n0)

def stage {D : Letters} (mu : D.Stages) (i : ℕ) : ℕ → ℤ := fun l => ent mu i (l + (i - D.n0))

def kaRows {D : Letters} (mu : D.Stages) (i : ℕ) : ℕ → ℤ := fun l => ent mu i (D.r + l)

def wt {D : Letters} (mu : D.Stages) : ℝ := weylDim D.K (kaRows mu D.Ns)

def Typical (D : Letters) (X : ℕ → ℝ) (mu : D.Stages) : Prop :=
  (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = false →
    ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) 0 - tailPos (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ X i) ∧
  (∀ i, D.r < i → i ≤ D.Ns → D.vec i = true →
    ((tailNeg (D.stLen (i - 1)) (stage mu (i - 1)) 0 - tailNeg (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ X i) ∧
  ∀ i, D.r < i → i ≤ D.Ns → (2 / 3 : ℝ) * (D.Bo i : ℝ) ≤ (ent mu (i - 1) (D.r - 1) : ℝ)

def Hyp (D : Letters) (a : ℝ) (p : ℕ) : Prop :=
  3 ≤ a ∧ p.Prime ∧ 13 ≤ p ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.k ≤ D.B i ∧ (D.B i : ℝ) ≤ 2 * a) ∧
  (∀ l, l + 1 < (D.latestV D.n0).length →
    p ^ 2 * (D.latestV D.n0).getD (l + 1) 0 ≤ 5 * (D.latestV D.n0).getD l 0) ∧
  (∀ l, l + 1 < (D.latestC D.n0).length →
    p ^ 2 * (D.latestC D.n0).getD (l + 1) 0 ≤ 5 * (D.latestC D.n0).getD l 0) ∧
  (∀ i, D.n0 - D.r < i → i ≤ D.n0 → D.vec i = true) ∧ D.Ns + D.r ≤ D.K ∧ 2 * D.r ≤ D.Ns ∧
  D.k ≤ 2 * (D.K - 2 * D.Ns) ∧ (D.Ns : ℝ) ≤ a

def k' (D : Letters) : ℕ := D.K - 2 * D.Ns

end Letters

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementL
section
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def SaturatedBasisExtension : Prop :=
  ∀ {O M1 M2 : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M1] [Module O M1] [Module.Free O M1] [Module.Finite O M1]
    [AddCommGroup M2] [Module O M2] [Module.Free O M2] [Module.Finite O M2] (ϖ : O), Irreducible ϖ →
    ∀ (Sp : Set M2) (abelian₂ : Submodule O M1) (Δ : M1 →ₗ[O] M2),
      (∀ x, ϖ • x ∈ abelian₂ → x ∈ abelian₂) →
      (∀ x, (∃ y, Δ x = ϖ • y) → ∃ x', x = ϖ • x') →
      (∀ u ∈ abelian₂, Δ u ∈ Submodule.span O Sp ⊔ (Ideal.span {ϖ}) • (⊤ : Submodule O M2)) →
      ∃ (R : ℕ) (g : Fin R → M2), (∀ i, g i ∈ Sp) ∧ LinearIndependent O g ∧
        (∃ T : Submodule O M2, IsCompl (Submodule.span O (Set.range g)) T) ∧
        Submodule.span O Sp ≤ Submodule.span O (Set.range g) ⊔ (Ideal.span {ϖ}) • (⊤ : Submodule O M2) ∧
        Module.finrank O abelian₂ ≤ R

def IsSat {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (N : Submodule O M) : Prop :=
  ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N

def SaturatedSubmoduleProperties : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O],
    (∀ {M : Type} [AddCommGroup M] [Module O M] (N N' : Submodule O M), IsSat N → IsSat N' → IsSat (N ⊓ N')) ∧
    (∀ {M ι : Type} [AddCommGroup M] [Module O M] (b : Module.Basis ι O M) (s : Set ι),
      IsSat (Submodule.span O (b '' s))) ∧
    (∀ {M : Type} [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (N : Submodule O M),
      IsSat N ↔ ∃ T : Submodule O M, IsCompl N T) ∧
    (∀ {M M' : Type} [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
      [AddCommGroup M'] [Module O M'] [Module.Free O M'] [Module.Finite O M']
      (N : Submodule O M) (N' : Submodule O M'), IsSat N → IsSat N' →
      IsSat (LinearMap.range (TensorProduct.map N.subtype N'.subtype)) ∧
      Module.finrank O (LinearMap.range (TensorProduct.map N.subtype N'.subtype)) =
        Module.finrank O N * Module.finrank O N')

abbrev CoarseVar (I1 I2 : Type) : Type := I1 ⊕ (I2 ⊕ I2)

def phC (O : Type) [CommRing O] {I1 I2 : Type} (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) :
    MvPolynomial (CoarseVar I1 I2) O →ₐ[O] MvPolynomial (I1 ⊕ I2) O :=
  MvPolynomial.aeval fun x => match x with
    | Sum.inl i => MvPolynomial.X (Sum.inl i) ^ P (Sum.inl i)
    | Sum.inr (Sum.inl i) => MvPolynomial.X (Sum.inr i) ^ P (Sum.inr i)
    | Sum.inr (Sum.inr i) => MvPolynomial.X (Sum.inr i) ^ (P (Sum.inr i) * Q i)

def MonomialDigitExpansion : Prop :=
  ∀ (O : Type) [CommRing O] [Nontrivial O] (I1 I2 : Type) (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ),
    (∀ i, 1 ≤ P i) → (∀ i, 1 ≤ Q i) →
    ∀ e : (I1 ⊕ I2) →₀ ℕ, ∃! ml : ((CoarseVar I1 I2) →₀ ℕ) × ((I1 ⊕ I2) →₀ ℕ),
      (∀ i, ml.1 (Sum.inr (Sum.inl i)) < Q i) ∧ (∀ i, ml.2 i < P i) ∧
      phC O P Q (MvPolynomial.monomial ml.1 1) * MvPolynomial.monomial ml.2 1 = MvPolynomial.monomial e 1

def CountL : Prop :=
  ∀ (k P n : ℕ), 1 ≤ k → 1 ≤ P →
    ∑ la ∈ (Finset.univ : Finset (Fin k → Fin P)).filter
        (fun la => (∑ c, (la c : ℕ)) ≤ n ∧ P ∣ n - ∑ c, (la c : ℕ)),
      ((n - ∑ c, (la c : ℕ)) / P + k - 1).choose (k - 1) = (n + k - 1).choose (k - 1)

def CountLa : Prop :=
  ∀ (k P n : ℕ), 1 ≤ k → 1 ≤ P →
    ((Finset.univ : Finset (Fin k → Fin P)).filter
      (fun la => (∑ c, (la c : ℕ)) % P = n % P)).card = P ^ (k - 1)

def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)

def FrobStep : Prop :=
  ∀ (p R : ℕ) (σ : Type) (f : MvPolynomial σ ℤ), p.Prime →
    ∃ h : MvPolynomial σ ℤ, MvPolynomial.expand (p ^ R) f = f ^ (p ^ R) + MvPolynomial.C (p : ℤ) * h

def DetPowNonzero : Prop :=
  ∀ (F : Type) [CommRing F] [Nontrivial F] (r : ℕ) (e : Fin r → ℕ), (∀ l, 1 ≤ e l) →
    (Matrix.of fun l c : Fin r => (MvPolynomial.X (l, c) : MvPolynomial (Fin r × Fin r) F) ^ e l).det ≠ 0

def CompareW : Prop :=
  ∀ (k Ns P n B : ℕ) (Y : ℝ), 1 ≤ k → 1 ≤ P → 1 ≤ Y →
    (n : ℝ) / P - 2 * k * Ns ≤ B → 7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ (n : ℝ) / P →
    ((n + k - 1).choose (k - 1) : ℝ) * (1 - 2 / (7.2 * Y)) ≤
      (P : ℝ) ^ (k - 1) * ((B + k - 1).choose (k - 1) : ℝ)

def CompareA : Prop :=
  ∀ (k a a' : ℕ), 1 ≤ k → 1 ≤ a → a' ≤ a →
    ((a + k - 1).choose (k - 1) : ℝ) * (1 - k * ((a : ℝ) - a') / a) ≤ ((a' + k - 1).choose (k - 1) : ℝ)

def TotalLoss : Prop :=
  ∀ (J r N : ℕ) (Y : ℝ), 2 ≤ r → 3 * J * r ≤ N → 0 < Y →
    (J : ℝ) / (32 * Y) + J * r * (0.28 + r / 2) / Y + N / (32 * Y) + N / Y ≤ N * r / Y

def PlanesLower : Prop :=
  ∀ (q r K : ℕ), 2 ≤ q →
    (q : ℝ) ^ (r * K) ≤ ∏ i ∈ range r, (((q : ℝ) ^ (r + K - i) - 1) / ((q : ℝ) ^ (r - i) - 1))

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementN
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Consequences : Prop :=
  ∀ (r K Ns p E0 mS : ℕ) (a Y Q : ℝ), 2 ≤ r → 4 * r ≤ Ns → 13 ≤ p → 1 ≤ Y → 1 ≤ Q →
    1088 * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
    32 * p * Y * ((r + K : ℕ) : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    8 ≤ Ns ∧ 416 ≤ a ∧ 1 ≤ Real.log a ∧ 1088 * Ns ^ 2 ≤ r + K ∧
    160 * (Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ∧ 5 * Ns ≤ r + K ∧ 32 * Y ≤ a ∧ 8 * (Ns : ℝ) ≤ a ∧
    32 * (E0 : ℝ) ≤ a ∧ r + K ≤ 2 * (K - 2 * Ns) ∧ Ns + r ≤ K

def PowMulFloorDivLe : Prop :=
  ∀ (p k Dt Do ao : ℕ) (a Y : ℝ), 1 ≤ p → 1 ≤ k → 0 < Y → Dt ≤ Do → (ao : ℝ) ≤ 2 * a →
    (p : ℝ) ^ Dt * (⌊((ao : ℝ) / (p : ℝ) ^ Do) / ((k : ℝ) ^ 2 * Y)⌋₊ : ℝ) ≤ 2 * a / ((k : ℝ) ^ 2 * Y)

def ReducedDegree : Prop :=
  ∀ (k Ns : ℕ) (a Y at' E' E0 Et : ℝ), 0 < Y → 1 ≤ k → 0 ≤ a → E' ≤ E0 → 32 * E0 ≤ a →
    Et ≤ 4 * Ns * a / ((k : ℝ) ^ 2 * Y) → 160 * (Ns : ℝ) ≤ (k : ℝ) ^ 2 * Y → a ≤ at' →
    (9 / 10 : ℝ) * at' ≤ at' - E' - Et

def CoarseExponentLowerBounds : Prop :=
  ∀ (p k Ns E0 mS R : ℕ) (a Y Q P1 : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 1 ≤ P1 → P1 ≤ Q →
    32 * p * Y * (k : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) < (p : ℝ) ^ (R + 1) →
    4 * Q * ((E0 : ℝ) + mS + 1) < (p : ℝ) ^ R ∧ 1 ≤ R ∧ (mS : ℝ) < (p : ℝ) ^ R

def CoarseScaleBounds : Prop :=
  ∀ (p k Ns D R : ℕ) (a Y P1 at' a' : ℝ), 1 ≤ p → 1 ≤ k → 1 ≤ Ns → 0 < Y → 0 < P1 →
    (p : ℝ) ^ R ≤ a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) → (p : ℝ) ^ D ≤ P1 → a ≤ at' → (9 / 10 : ℝ) * at' ≤ a' →
    8 * Y * (k : ℝ) ^ 2 * Ns ≤ at' / (p : ℝ) ^ (D + R) ∧ 7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ a' / (p : ℝ) ^ (D + R)

def CoarseExponentCompare : Prop :=
  ∀ (p k Ns D1 L1 R R' dn : ℕ) (a Y P1 : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 0 < Y → 0 < a →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ dn)) < (p : ℝ) ^ R' →
    (p : ℝ) ^ R ≤ a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) → (p : ℝ) ^ (D1 + L1 + 1) ≤ P1 →
    (p : ℝ) ^ L1 < (p : ℝ) ^ dn * (p : ℝ) ^ R' / (p : ℝ) ^ R ∧ R + L1 < dn + R'

def CyclicProductRatio : Prop :=
  ∀ (J : ℕ) [NeZero J] (Qs ρ : Fin J → ℝ), (∀ j, ρ j ≠ 0) →
    ∏ j : Fin J, (Qs (j + 1) * ρ (j + 1) / ρ j) = ∏ j : Fin J, Qs j

def BackThreshold : Prop :=
  ∀ (k r Ns : ℕ) (Y co th : ℝ), 3 ≤ k → r ≤ k → 8 ≤ Ns → 1 ≤ Y → 8 * Y * (k : ℝ) ^ 2 * Ns ≤ co →
    (2 / 3 : ℝ) * (0.9 * co - ((k : ℝ) + r + 2) - ((k : ℝ) * Ns + 1)) ≤ th →
    co / 2 ≤ th - (k : ℝ) * Ns

def BackMargin : Prop :=
  ∀ (k Ns : ℕ) (pR nu ka dS dV mS s : ℝ), 0 < pR → ka + ((k : ℝ) * Ns + 1) ≤ nu → dS + dV < (k : ℝ) * Ns * pR →
    mS < pR → (pR * ka + dV) + mS + s < pR * nu - dS + s

def OrderBounds : Prop :=
  ∀ (p k Ns D Do L1 R : ℕ) (a Y P1 La : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 ≤ a → 0 ≤ La →
    (p : ℝ) ^ R ≤ a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) → (p : ℝ) ^ (D + L1 + 1) ≤ P1 → D + L1 + 1 ≤ Do →
    (k : ℝ) * (p : ℝ) ^ R ≤ a / (p : ℝ) ^ (L1 + D + 1) / (8 * Y * k * Ns) ∧
    (p : ℝ) ^ R * (La * a / (p * k * (p : ℝ) ^ (D + R))) + k * (p : ℝ) ^ R ≤
      La * a / (p * k * (p : ℝ) ^ D) + a / (p : ℝ) ^ (L1 + D) ∧
    (p : ℝ) ^ R * (La * a / (p * k * (p : ℝ) ^ (D + R)) + 4 * a / (p : ℝ) ^ (Do + R)) + k * (p : ℝ) ^ R ≤
      La * a / (p * k * (p : ℝ) ^ D) + 10 * a / (p : ℝ) ^ (L1 + D)

def DegreeBound : Prop :=
  ∀ (p k L1 N : ℕ) (a La Q : ℝ) (D : Fin N → ℕ) (o lab : Fin N → ℝ), 1 ≤ p → 1 ≤ k → 0 ≤ a → 0 ≤ La →
    (∀ z, (p : ℝ) ^ D z ≤ Q) →
    (∀ z, o z ≤ La * a / (p * k * (p : ℝ) ^ D z) + 10 * a / (p : ℝ) ^ (L1 + D z)) →
    (∀ z, lab z ≤ k * (p : ℝ) ^ D z) →
    ∑ z, ((p : ℝ) ^ D z * o z + lab z) ≤ N * (La * a / (p * k) + 10 * a / (p : ℝ) ^ L1 + k * Q)

def AdmissibleFloor : Prop :=
  ∀ (k r Ns : ℕ) (a Y c : ℝ) (B : ℤ), 10 ≤ k → r ≤ k → 8 ≤ Ns → 1 ≤ Y → 7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ c → c ≤ 2 * a →
    (B = ⌊c⌋ - ((k : ℤ) + r + 1) - ((k : ℤ) * Ns + 1) ∨ (c - k < (B : ℝ) ∧ (B : ℝ) ≤ c)) →
    c - 2 * k * Ns ≤ (B : ℝ) ∧ (B : ℝ) ≤ c ∧ 7 * Y * (k : ℝ) ^ 2 * Ns ≤ (B : ℝ) ∧ (k : ℝ) ≤ (B : ℝ) ∧ (B : ℝ) ≤ 2 * a

def AdmissibleRatio : Prop :=
  ∀ (p k Ns D D' R : ℕ) (a Y a1 a2 B B' : ℝ), 2 ≤ p → 10 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → D' + 2 ≤ D →
    0.9 * a ≤ a1 → a1 ≤ 2 * a → 0.9 * a ≤ a2 → a2 ≤ 2 * a →
    7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ a2 / (p : ℝ) ^ (D' + R) →
    B ≤ a1 / (p : ℝ) ^ (D + R) → a2 / (p : ℝ) ^ (D' + R) - 2 * k * Ns ≤ B' →
    (p : ℝ) ^ 2 * B ≤ 5 * B'

def AdmissibleBoundOfLargerExponent : Prop :=
  ∀ (p D D' R : ℕ) (a a2 B' : ℝ), 1 ≤ p → 0 ≤ a → D + 1 ≤ D' → a2 ≤ 2 * a → B' ≤ a2 / (p : ℝ) ^ (D' + R) →
    B' ≤ 2 * (a / (p : ℝ) ^ (D + R)) / p ∧ 2 * (a / (p : ℝ) ^ (D + R)) / p ≤ 4 * (a / (p : ℝ) ^ (D + R)) / p

def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0

def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)

def PaddingDegreeBounds : Prop :=
  ∀ (k r : ℕ) (Q' nv e de : ℤ) (c : ℝ), (k : ℤ) < Q' → c - (k : ℝ) / Q' < (nv : ℝ) / Q' → (nv : ℝ) / Q' ≤ c →
    0 ≤ e → e < r * Q' → nv - e = Q' * (de + (⌊c⌋ - ((k : ℤ) + r + 1))) →
    (k : ℤ) < de ∧ de < (k : ℤ) + r + 2

def FinalProduct : Prop :=
  ∀ (J r N Ns k : ℕ) (a Y E0 : ℝ), 2 ≤ r → 3 * J * r ≤ N → 0 < Y → (N : ℝ) * r / Y < 1 → 32 * Y ≤ a → 1 ≤ Ns →
    4 * Ns ≤ k → 0 ≤ E0 → k * E0 / a ≤ 1 / (32 * Y) →
    1 - (N : ℝ) * r / Y ≤
      (1 - (a ^ (Ns ^ 2))⁻¹) ^ J * (1 - 0.28 / Y) ^ (J * r) * (1 - r / (2 * Y)) ^ (J * r) *
        (1 - k * E0 / a - 4 * Ns / (k * Y)) ^ N

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end


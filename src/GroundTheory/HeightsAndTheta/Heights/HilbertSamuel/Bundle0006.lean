import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjectiveSpaceIncrementHyp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]

open Classical in

structure IsMultigraded (ℳ : (K → ℤ) → Submodule F M) : Prop where
  internal : DirectSum.IsInternal ℳ
  var_mul : ∀ (v : Σ k, ι k) (m : K → ℤ), ∀ x ∈ ℳ m,
    (X v : MRing ι F) • x ∈ ℳ (m + Pi.single v.1 1)

variable {ι}

def modHilb (ℳ : (K → ℤ) → Submodule F M) (m : K → ℤ) : ℤ :=
  (Module.finrank F (ℳ m) : ℤ)

end Objects

section Support

variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]

def modMultAt (p : PrimeSpectrum S) : ℕ∞ :=
  Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

end Support

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]

def topSupport (d : ℕ) : Set (PrimeSpectrum (MRing ι F)) :=
  {p | p ∈ Module.support (MRing ι F) M ∧ IsMultiProjPrime p.asIdeal ∧
    ringKrullDim (MRing ι F ⧸ p.asIdeal) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)}

def modIntNum (d : ℕ) (a : K → ℤ) : ℤ :=
  ∑ᶠ (p : PrimeSpectrum (MRing ι F)) (_ : p ∈ topSupport ι F M d),
    ((modMultAt M p).toNat : ℤ) * intNum F p.asIdeal (fun _ : Fin d => a)

end Cycle

def degSize {K : Type*} [Fintype K] (a : K → ℤ) : ℝ := ∑ k, (a k : ℝ)

section Statements

def MultigradedFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type u) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] (ℳ : (K → ℤ) → Submodule F M),
    IsMultigraded ι ℳ → Module.Finite (MRing ι F) M →
    ∃ (n : ℕ) (x : Fin n → M) (c : Fin n → K → ℤ) (q : Fin n → Ideal (MRing ι F)),
      (∀ j, x j ∈ ℳ (c j)) ∧
      (∀ j, (q j).IsPrime ∧ IsMultiHomogIdeal (q j)) ∧
      Submodule.span (MRing ι F) (Set.range x) = ⊤ ∧
      ∀ j (f : MRing ι F),
        f • x j ∈ Submodule.span (MRing ι F) (x '' {i | i < j}) ↔ f ∈ q j

def HilbertDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ a₀ : ℕ, ∀ a : K → ℤ, (∀ k, (a₀ : ℤ) ≤ a k) →
      hilbFn q a = intNum F q (Fin.elim0 : Fin 0 → K → ℤ)

def HilbertPrime.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℤ, (∀ k, (a₀ : ℤ) ≤ a k) →
      |(hilbFn q a : ℝ) - (intNum F q (fun _ : Fin d => a) : ℝ) / (d.factorial : ℝ)| ≤
        C * (degSize a + 1) ^ ((d : ℤ) - 1)

def HilbertModule.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type u) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] (ℳ : (K → ℤ) → Submodule F M) (d : ℕ),
    IsMultigraded ι ℳ → Module.Finite (MRing ι F) M →
    (∀ p ∈ Module.support (MRing ι F) M, IsMultiProjPrime p.asIdeal →
      ringKrullDim (MRing ι F ⧸ p.asIdeal) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℤ, (∀ k, (a₀ : ℤ) ≤ a k) →
      |(modHilb ℳ a : ℝ) - (modIntNum ι F M d a : ℝ) / (d.factorial : ℝ)| ≤
        C * (degSize a + 1) ^ ((d : ℤ) - 1)

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

def RankOfSections.Statement : Prop :=
  ∀ (ι : Unit → Type) [∀ k, Fintype (ι k)] (D : ℕ) (q : Ideal (MRing ι ℚ)),
    IsMultiProjPrime q → ringKrullDim (MRing ι ℚ ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    (fun n : ℕ => (hilbFn q (fun _ => (n : ℤ)) : ℝ) -
        (intNum ℚ q (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ ((D : ℤ) - 1)

def MixedNumberPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ), intNum F q (bs ∘ σ) = intNum F q bs) ∧
    ∀ (bs : Fin d → K → ℤ) (j : Fin d) (b b' : K → ℤ),
      intNum F q (Function.update bs j (b + b')) =
        intNum F q (Function.update bs j b) + intNum F q (Function.update bs j b')

end Statements

section Examples

variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]

def blockWeightInt : (Σ k, ι k) → K → ℤ := fun v => Pi.single v.1 1

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

section Objects

variable {K : Type*} [DecidableEq K]

def unitDeg (k : K) : K → ℤ := Pi.single k 1

variable [Fintype K] {ι : K → Type*} {F : Type*} [Field F]

structure IsMultigrading (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    (piece : (K → ℤ) → Submodule F M) : Prop where
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (v : Σ k, ι k) (m : K → ℤ) (x : M), x ∈ piece m →
    (X v : MRing ι F) • x ∈ piece (m + unitDeg v.1)

def modMultAt {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module (MRing ι R) M]
    (W : Ideal (MRing ι R)) [W.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M)

open Classical in

def topCycleNum (F : Type*) [Field F] (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] (d : ℕ) (bs : Fin d → K → ℤ) :
    ℤ :=
  ∑ᶠ W : Ideal (MRing ι F),
    if h : IsMultiProjPrime W ∧ Module.annihilator (MRing ι F) M ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
      haveI : W.IsPrime := h.1.isPrime
      ((modMultAt M W).toNat : ℤ) * intNum F W bs
    else 0

end Objects

def MultigradedFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (MRing ι F)),
      N 0 = ⊥ ∧ N (Fin.last n) = ⊤ ∧
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j) ∧
      ∀ (W : Ideal (MRing ι F)) (hW : W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes),
        (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
          haveI : W.IsPrime := hW.1.1
          modMultAt M W

def HilbertDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      hilbFn q (fun k => (a k : ℤ)) = intNum F q (![] : Fin 0 → K → ℤ)

def HilbertPrime.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(hilbFn q (fun k => (a k : ℤ)) : ℝ) -
          (intNum F q (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

def HilbertPrime.Statement : Prop := ∀ d : ℕ, HilbertPrime.AtDim.{u} d

def HilbertModule.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → Module.annihilator (MRing ι F) M ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) -
          (topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

def HilbertModule.Statement : Prop := ∀ d : ℕ, HilbertModule.AtDim.{u, v} d

def ModulesFromPrimes.Statement : Prop :=
  ∀ d : ℕ, (∀ e ≤ d, HilbertPrime.AtDim.{u} e) → HilbertModule.AtDim.{u, v} d

def HilbertIncrement.Statement : Prop :=
  ∀ d : ℕ, HilbertModule.AtDim.{u, u} d →
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ b : K, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |((hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) : ℤ) : ℝ) -
          (intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) /
            d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

open Classical in

def IntersectionRecursion.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b : K) (i : ι b), (X ⟨b, i⟩ : MRing ι F) ∉ q → ∀ bs : Fin d → K → ℤ,
      intNum F q (Matrix.vecCons (unitDeg b) bs) =
        ∑ᶠ W : Ideal (MRing ι F),
          if h : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
              ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
            haveI : W.IsPrime := h.1.isPrime
            ((multAt (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) W).toNat : ℤ) * intNum F W bs
          else 0

def MixedNumberPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ), intNum F q (bs ∘ σ) = intNum F q bs) ∧
    ∀ (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ),
      intNum F q (Function.update bs j (x + y)) =
        intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y)

def MultigradedHilbertPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (p : MvPolynomial K ℚ) (a₀ : ℕ), p.totalDegree ≤ d ∧
      ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
        (hilbFn q (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p

def RankOfSections.Statement : Prop :=
  ∀ (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) ℚ)) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    ∃ C : ℝ, ∀ n : ℕ,
      |(hilbFn q (fun _ => (n : ℤ)) : ℝ) -
          (intNum ℚ q (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1)

section Examples

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type u} [Field F]

def intWeight : (Σ k, ι k) → K → ℤ := fun v => unitDeg v.1

def ringPiece (m : K → ℤ) : Submodule F (MRing ι F) :=
  weightedHomogeneousSubmodule F (intWeight (ι := ι)) m

omit [∀ k, Fintype (ι k)] in

theorem isMultigrading_ring : IsMultigrading ι (MRing ι F) (ringPiece (F := F) (ι := ι)) where
  internal := (weightedDecomposition F (intWeight (ι := ι))).isInternal
  smul_mem := by
    intro v m x hx
    rw [smul_eq_mul]
    have hX : IsWeightedHomogeneous (intWeight (ι := ι)) (X v : MRing ι F) (unitDeg v.1) :=
      isWeightedHomogeneous_X F _ v
    have := hX.mul hx
    change X v * x ∈ weightedHomogeneousSubmodule F intWeight (m + unitDeg v.1)
    rw [mem_weightedHomogeneousSubmodule, add_comm]
    exact this

end Examples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end


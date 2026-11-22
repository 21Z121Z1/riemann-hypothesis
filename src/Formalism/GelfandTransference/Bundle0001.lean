import Mathlib

-- bundled from Formalism.GelfandTransference.EnergyIdentity
section
open Finset

noncomputable section

namespace Formalism.HadamardInequality

def grass (F V : Type) [Field F] [AddCommGroup V] [Module F V] (u : ℕ) : Type :=
  {U : Submodule F V // Module.finrank F U = u}

def GrassFormula : Prop :=
  ∀ (F V : Type) [Field F] [Fintype F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (u : ℕ), u ≤ Module.finrank F V →
    Nat.card (grass F V u) * ∏ i ∈ range u, (Fintype.card F ^ u - Fintype.card F ^ i) =
      ∏ i ∈ range u, (Fintype.card F ^ Module.finrank F V - Fintype.card F ^ i)

def GrassBound : Prop :=
  ∀ (F V : Type) [Field F] [Fintype F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (u : ℕ), u ≤ Module.finrank F V →
    (Nat.card (grass F V u) : ℝ) ≤ 4 * (Fintype.card F : ℝ) ^ (u * (Module.finrank F V - u))

def energy {m : ℕ} (u : Fin m → ℕ) : ℤ :=
  ∑ j, (u j : ℤ) ^ 2 - ∑ j : Fin m, ∑ i : Fin m, if (i : ℕ) + 1 = j then (u i : ℤ) * u j else 0

def EnergyIdentity : Prop :=
  ∀ (m : ℕ) (u : Fin (m + 1) → ℕ),
    2 * energy u = (u 0 : ℤ) ^ 2 +
      (∑ j : Fin (m + 1), ∑ i : Fin (m + 1),
        if (i : ℕ) + 1 = j then ((u j : ℤ) - u i) ^ 2 else 0) + (u (Fin.last m) : ℤ) ^ 2

def EnergyPos : Prop :=
  ∀ (m : ℕ) (u : Fin m → ℕ), u ≠ 0 → 1 ≤ energy u

def ChainExponent : Prop :=
  ∀ (m : ℕ) (u : Fin m → ℕ) (cs : Fin m → ℝ) (c : ℝ), (∀ j, c ≤ cs j) → u ≠ 0 →
    1 + c * (∑ j, (u j : ℝ)) ≤ (∑ j, cs j * u j) + (energy u : ℝ)

def qbinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qbinom q n k + q ^ (k + 1) * qbinom q n (k + 1)

def QBinomialIdentity : Prop :=
  ∀ q k : ℕ, ∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * (q : ℤ) ^ Nat.choose i 2 * (qbinom q k i : ℤ) =
    if k = 0 then 1 else 0

def SubspaceCount : Prop :=
  ∀ (F V : Type) [Field F] [Fintype F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (i : ℕ), Nat.card (grass F V i) = qbinom (Fintype.card F) (Module.finrank F V) i

def MoebiusSub : Prop :=
  ∀ (F V : Type) [Field F] [Fintype F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype V] (X : Submodule F V),
    (∑ᶠ (U : Submodule F V) (_ : X ≤ U),
      (-1 : ℤ) ^ (Module.finrank F V - Module.finrank F U) *
        (Fintype.card F : ℤ) ^ Nat.choose (Module.finrank F V - Module.finrank F U) 2) =
      if X = ⊤ then 1 else 0

def succMin {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : Submodule ℤ E)
    (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ v : Fin i → E, (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ r}

def zdual {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : Submodule ℤ E) :
    Submodule ℤ E where
  carrier := {y | ∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩
  zero_mem' := by intro x _; exact ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨z, h⟩ := ha x hx
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, inner_smul_right, h]; push_cast; ring⟩

def Transference : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℤ E), DiscreteTopology M → Submodule.span ℝ (M : Set E) = ⊤ →
    ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank ℝ E →
      succMin (zdual M) i * succMin M (Module.finrank ℝ E + 1 - i) ≤
        (Module.finrank ℝ E : ℝ) ^ 2

end Formalism.HadamardInequality
end
end

-- bundled from Formalism.GelfandTransference.GelfandCentral
section
open Finset

noncomputable section

namespace Formalism.HadamardInequality

def GlRel {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

def epow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | k + 1, a, b => ∑ c, E a c * epow E k c b

def etr {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) : A := ∑ a, epow E k a a

def GelfandCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (c d : Fin n), etr E k * E c d = E c d * etr E k

def HighestDiag : Prop :=
  ∀ (A M : Type) [Ring A] [AddCommGroup M] [Module A M] (n : ℕ) (E : Fin n → Fin n → A),
    GlRel E → ∀ (ν : Fin n → ℤ) (v : M),
    (∀ a b : Fin n, a < b → E a b • v = 0) → (∀ a : Fin n, E a a • v = ν a • v) →
    ∀ (k : ℕ) (a : Fin n),
      epow E (k + 1) a a • v =
        (ν a + (n : ℤ) - 1 - (a : ℤ)) • (epow E k a a • v) -
          ∑ b ∈ univ.filter (fun b : Fin n => a < b), epow E k b b • v

end Formalism.HadamardInequality
end
end


import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Formalism.RealPlaceAnalysis.StatementC
section
open Finset

noncomputable section

namespace Formalism.REAL

def cyc {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W}

def cval {n : ℕ} (ν : Fin n → ℂ) : ℂ :=
  ∑ a, ν a ^ 2 + ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (ν a - ν b)

def chamber {n : ℕ} (G : Fin n → Fin n → ℤ) : Set (Fin n → ℤ) :=
  {m | ∀ a b, a < b → G a b ≤ m a - m b}

def CasHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → Cas E v = cval ν • v

def CasCyc : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, Cas E x = cval ν • x

def CharId : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, ∀ a b : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b x = 0

def DegVand : Prop :=
  ∀ (n : ℕ) (c : ℂ) (G : Fin n → Fin n → ℤ) (f : (Fin n → ℤ) → ℂ),
    (∀ a b, a < b → 1 ≤ G a b) →
    (∀ (m : Fin n → ℤ) (s : Fin n), m ∈ chamber G → m - Pi.single s 1 ∈ chamber G →
      f (m - Pi.single s 1) = Dfac (fun a => c + (m a : ℂ)) s * f m) →
    ∀ m m', m ∈ chamber G → m' ∈ chamber G →
      f m * vand (fun a => c + (m' a : ℂ)) = f m' * vand (fun a => c + (m a : ℂ))

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.StatementE
section
open Finset

noncomputable section

namespace Formalism.REAL

def Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) : A :=
  (if a = b then algebraMap ℂ A u else 0) + E a b

def qminor {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod

def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E id id u

def RTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (x y : ℂ) (a b c d : Fin n),
      algebraMap ℂ A (x - y) * (Tm E x a b * Tm E y c d - Tm E y c d * Tm E x a b) =
        Tm E x c b * Tm E y a d - Tm E y c b * Tm E x a d

def QSkewRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n)
    (τ : Equiv.Perm (Fin t)) (u : ℂ),
    qminor E (a ∘ τ) b u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u

def QSkewCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (τ : Equiv.Perm (Fin t)) (u : ℂ),
      qminor E a (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u

def QDetCentral : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (u : ℂ) (c d : Fin n), qdet E u * E c d = E c d * qdet E u

def QDetHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ u : ℂ, qdet E u v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v

def QComatrix : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
    ∀ (u : ℂ) (i l : Fin (m + 1)),
      ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
          qminor E (Fin.succAbove j) (Fin.succAbove i) u * Tm E (u - (m : ℂ)) j l =
        if i = l then qdet E u else 0

end Formalism.REAL
end
end


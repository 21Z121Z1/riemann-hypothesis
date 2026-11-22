import Mathlib

-- bundled from Formalism.LocalToGlobal.AdelicCompactOpens.GLintCompactOpen
section
namespace Formalism.L2.Props

open Matrix

def GLintCompactOpen : Prop :=
  ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (O : Subring R),
    IsOpen (O : Set R) → IsCompact (O : Set R) → ∀ n : ℕ,
      IsOpen {g : GL (Fin n) R | (∀ a b, (g : Matrix (Fin n) (Fin n) R) a b ∈ O) ∧
          ∀ a b, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b ∈ O} ∧
      IsCompact {g : GL (Fin n) R | (∀ a b, (g : Matrix (Fin n) (Fin n) R) a b ∈ O) ∧
          ∀ a b, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b ∈ O}

section uni

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ}

def ParaR (r : ℕ) (h : GL (Fin n) K) : Prop :=
  (∀ a b, Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) ≤ 1) ∧
    (∀ a b, Valued.v (((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) ≤ 1) ∧
    ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) < 1

def UniR (r : ℕ) (h : GL (Fin n) K) : Prop :=
  ParaR r h ∧ ∀ a b : Fin n, a.val < r → b.val < r →
    (b.val < a.val → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) < 1) ∧
    (a = b → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b - 1) < 1)

def detDDR (r : ℕ) (h : GL (Fin n) K) : K :=
  (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => (h : Matrix (Fin n) (Fin n) K) a.1 b.1).det

def supDiagR (r : ℕ) (h : GL (Fin n) K) : K :=
  ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then (h : Matrix (Fin n) (Fin n) K) a b else 0

end uni

def ParaDetUnit : Prop :=
  ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (n r : ℕ) (h : GL (Fin n) K), ParaR r h → Valued.v (detDDR r h) = 1

def UniCharMul : Prop :=
  ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (n r : ℕ) (ψ₀ : AddChar K ℂ) (ξ : Kˣ →* ℂˣ),
    (∀ x : K, Valued.v x < 1 → ψ₀ x = 1) → (∀ u : Kˣ, Valued.v ((u : K) - 1) < 1 → ξ u = 1) →
    ∀ (g h : GL (Fin n) K) (ug uh ugh : Kˣ), UniR r g → UniR r h →
      (ug : K) = detDDR r g → (uh : K) = detDDR r h → (ugh : K) = detDDR r (g * h) →
      ψ₀ (supDiagR r (g * h)) * (ξ ugh : ℂ) = (ψ₀ (supDiagR r g) * (ξ ug : ℂ)) * (ψ₀ (supDiagR r h) * (ξ uh : ℂ))

end Formalism.L2.Props
end

-- bundled from Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily
section
namespace Formalism.L2.Props

open Matrix
open scoped ComplexOrder

def PolyDenseZero : Prop :=
  ∀ (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) (S : Set (σ → ℂ)), Dense S →
    (∀ x ∈ S, MvPolynomial.eval x p = 0) → p = 0

def HermDefON : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef → ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1

def HermConjExists : Prop :=
  ∀ (E : Type) [Field E] [CharZero E] (σ : E →+* E), (∀ x, σ (σ x) = x) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (J.map σ)ᵀ = J →
      ∃ P : Matrix (Fin n) (Fin n) E, (P.map σ)ᵀ * J * P = J.map σ

def DiagConj : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
    (∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (P : Matrix (Fin n) (Fin n) ℂ) * A * (P⁻¹ : GL (Fin n) ℂ) = diagonal d) →
    (∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (P : Matrix (Fin n) (Fin n) ℂ) * B * (P⁻¹ : GL (Fin n) ℂ) = diagonal d) →
    A.charpoly = B.charpoly →
    ∃ Q : GL (Fin n) ℂ, (Q : Matrix (Fin n) (Fin n) ℂ) * A * (Q⁻¹ : GL (Fin n) ℂ) = B

end Formalism.L2.Props
end

-- bundled from Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen
section
namespace Formalism.L2.Props

open Filter Topology IsDedekindDomain NumberField

def LogCycConv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ L : ℚ_[l],
    Tendsto (fun k : ℕ => ((((u : ℤ_[l]) : ℚ_[l]) ^ ((l - 1) * l ^ k) - 1) / (((l - 1) * l ^ k : ℕ) : ℚ_[l])))
      atTop (𝓝 L)

def PlaceEmbExists : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    (∀ x : F, algebraMap F Ω x ∈ A ↔ v.valuation F x ≤ 1) →
    ∃ i : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F), ∀ x : Ω, x ∈ A ↔
      ∃ q : Polynomial (v.adicCompletion F), q.Monic ∧ (∀ k, q.coeff k ∈ v.adicCompletionIntegers F) ∧
        Polynomial.aeval (i x) q = 0

def IntAdelesCompactOpen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} ∧
    IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

def TameTrivOnZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime →
    Nat.card (𝓞 E ⧸ v.asIdeal) = g →
    ∀ ξ : (v.adicCompletion E)ˣ →* ℂˣ,
      (∀ u : (v.adicCompletion E)ˣ, Valued.v ((u : v.adicCompletion E) - 1) < 1 → ξ u = 1) →
      (∀ (m : ℤ) (u : (v.adicCompletion E)ˣ), ¬ (g : ℤ) ∣ m → (u : v.adicCompletion E) = (m : v.adicCompletion E) → ξ u = 1) →
      ∀ u : (v.adicCompletion E)ˣ, Valued.v (u : v.adicCompletion E) = 1 → ξ u = 1

end Formalism.L2.Props
end

